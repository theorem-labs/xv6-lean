import MachCSL.Logic.FsBitmapSpec
import MachCSL.Logic.FsBytesGammaProofs
import MachCSL.Logic.FsStateBitmapProofs
import Xv6.Fs.SnapshotConfigBlockProofs

namespace MachCSL.Logic.FsBitmap
open Iris Iris.Std Iris.BI Xv6.Fs DurableState SnapshotConfig
variable {GF : BundledGFunctors}

theorem freeSet_filter size used : freeSet size used =
    FiniteSet.filter (fun b => decide (b ∉ used)) (LawfulSet.ofList (FsState.poolIndices size) : BlockSet) := by
  apply _root_.Std.ExtTreeSet.ext_mem
  intro b
  rw [elem_of_free_set, FiniteSet.mem_filter, ← LawfulSet.mem_ofList, FsState.poolIndices_mem]
  simp

/-- The source free-pool introduction, valid for arbitrary signed size. -/
theorem free_pool_intro (view : FsView.View GF) size used :
    bigSepS (fun b => iprop(∃ bytes, FsView.blockOwned view b bytes)) (freeSet size used) ⊢ FsState.freePool view size used := by
  rw [freeSet_filter, (BigSepS.bigSepS_filter_cond (fun b => decide (b ∉ used))).to_eq]
  have same : (fun b => if decide (b ∉ used) then iprop(∃ bytes, FsView.blockOwned view b bytes) else emp) =
      FsState.poolElt view used := by
    funext b
    by_cases member : b ∈ used <;> simp [FsState.poolElt, member]
  rw [same]
  have nodup : (FsState.poolIndices size).Nodup :=
    List.nodup_range.map Int.ofNat (fun a b different same => different (Int.ofNat.inj same))
  exact (BigSepS.bigSepS_of_list (S := BlockSet) (Φ := FsState.poolElt view used) nodup).mp

variable (dc : Disk.Capacity GF)

theorem bitmap_res_open names bitmapBlock size used :
    resource dc names bitmapBlock size used ⊣⊢
      FsBlocks.block dc names.bytes bitmapBlock (BitmapEncoding.bitmapBytes 1024 used) ∗
        FsState.freePool (FsBytesGamma.logged dc names) size used := by
  unfold resource FsState.freeBitmapAt
  rw [(FsBytesGamma.block dc names bitmapBlock _).to_eq]
  exact .rfl

instance resource_timeless names bitmapBlock size used : Timeless (resource dc names bitmapBlock size used) := by
  unfold resource
  infer_instance

theorem bitmap_res_of_snap names state image home
    (bytes : Snapshot.Bytes state (SnapshotHome.restrict image home)) :
    bigSepS (fun b => FsBlocks.block dc names.bytes b (image b)) (bitmapSpent state) ⊢
      resource dc names state.superblock.bmapstart state.superblock.size state.used := by
  have used : state.superblock.bmapstart ∈ state.used :=
    bytes.metadataUsed _ (Or.inr (Or.inl rfl))
  have disjoint : ((∅ : BlockSet).insert state.superblock.bmapstart) ## (freeSet state.superblock.size state.used) := by
    intro b ⟨left, right⟩
    have equal : b = state.superblock.bmapstart := by
      have same : state.superblock.bmapstart = b := by
        simpa only [_root_.Std.ExtTreeSet.mem_insert, _root_.Std.ExtTreeSet.not_mem_empty, _root_.or_false,
          _root_.Std.compare_eq_eq_iff_eq] using left
      exact same.symm
    subst b
    exact ((elem_of_free_set _ _ _).mp right).2 used
  have encoded : image state.superblock.bmapstart = BitmapEncoding.bitmapBytes 1024 state.used :=
    ((SnapshotHome.restrict_lookup_some image home _ _).mp bytes.bitmap).2.symm
  iintro H
  iunfold bitmapSpent at H
  ihave ⟨Hbitmap, Hpool⟩ := (BigSepS.bigSepS_union (Φ := fun b => FsBlocks.block dc names.bytes b (image b)) disjoint).mp $$ H
  have singleton : bigSepS (fun b => FsBlocks.block dc names.bytes b (image b)) ((∅ : BlockSet).insert state.superblock.bmapstart) ⊣⊢
      FsBlocks.block dc names.bytes state.superblock.bmapstart (image state.superblock.bmapstart) := by
    have equal : ((∅ : BlockSet).insert state.superblock.bmapstart) = ({state.superblock.bmapstart} : BlockSet) := by
      apply _root_.Std.ExtTreeSet.ext_mem
      intro b
      simp only [_root_.Std.ExtTreeSet.mem_insert, _root_.Std.ExtTreeSet.not_mem_empty, _root_.or_false,
        _root_.Std.compare_eq_eq_iff_eq, LawfulSet.mem_singleton]
      exact eq_comm
    rw [equal]
    exact BigSepS.bigSepS_singleton
  ihave Hbitmap := singleton.mp $$ Hbitmap
  have lift : bigSepS (fun b => FsBlocks.block dc names.bytes b (image b)) (freeSet state.superblock.size state.used) ⊢
      bigSepS (fun b => iprop(∃ data, FsView.blockOwned (FsBytesGamma.logged dc names) b data)) (freeSet state.superblock.size state.used) := by
    apply BigSepS.bigSepS_mono
    intro b _
    iintro Hb
    iexists image b
    iapply (FsBytesGamma.block dc names b _).mpr $$ Hb
  ihave Hpool := lift $$ Hpool
  ihave Hpool := free_pool_intro (FsBytesGamma.logged dc names) state.superblock.size state.used $$ Hpool
  iapply (bitmap_res_open dc names _ _ _).mpr
  have rewriteBitmap : FsBlocks.block dc names.bytes state.superblock.bmapstart (image state.superblock.bmapstart) =
      FsBlocks.block dc names.bytes state.superblock.bmapstart (BitmapEncoding.bitmapBytes 1024 state.used) := by rw [encoded]
  ihave Hbitmap := (BIBase.BiEntails.of_eq rewriteBitmap).mp $$ Hbitmap
  iframe Hbitmap Hpool

theorem actual : Spec dc where
  poolIntro := free_pool_intro
  openResource := bitmap_res_open dc
  ofSnapshot := bitmap_res_of_snap dc

end MachCSL.Logic.FsBitmap
