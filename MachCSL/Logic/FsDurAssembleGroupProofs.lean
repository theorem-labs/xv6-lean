import MachCSL.Logic.FsDurAssembleSpec
import MachCSL.Logic.FsDurAllocLedgerProofs
import MachCSL.Logic.FsStateProofs

namespace MachCSL.Logic.FsDurAssemble
open Iris Iris.Std Iris.BI Xv6.Fs DurableState DurableNode FsView FsDurAlloc
variable {GF : BundledGFunctors} (view : View GF)

/-- The source elements-of-domain bridge, with the same concrete finite map
and a key-only predicate. No value or empty entry is erased from the map. -/
theorem keys_map {K V : Type} [Ord K] [_root_.Std.TransOrd K] [_root_.Std.LawfulEqOrd K]
    (map : _root_.Std.ExtTreeMap K V) (P : K → IProp GF) :
    bigSepL (fun _ key => P key) map.keys ⊣⊢
      bigSepM (M := _root_.Std.ExtTreeMap K) (fun key _ => P key) map := by
  rw [← _root_.Std.ExtTreeMap.map_fst_toList_eq_keys, BigSepL.bigSepL_map]
  exact (BigSepM.bigSepM_toList (M := _root_.Std.ExtTreeMap K) (m := map) (Φ := fun key _ => P key)).symm

theorem slots_grouped (state : State) disk : slotLedger view state disk ⊣⊢
    byteRange view 1 0 state.superblockBytes ∗
    byteRange view state.superblock.bmapstart 0 (BitmapEncoding.bitmapBytes 1024 state.used) ∗
    (((bigSepM (M := FsState.InodeMap) (fun i _ => byteRange view
        (fpBlock state (.record i)) (fpOffset (.record i)) (fpBytes state disk (.record i))) state.inodes ∗
      bigSepM (M := FsState.InodeMap) (fun i _ =>
        bigSepM (M := FsState.SlotMap) (fun k _ => byteRange view
          (fpBlock state (.data i k)) 0 (fpBytes state disk (.data i k))) (nodeAt state i).blocks) state.inodes) ∗
      bigSepM (M := FsState.InodeMap) (fun i _ => byteRange view
        (fpBlock state (.indirect i)) 0 (fpBytes state disk (.indirect i))) state.inodes) ∗
      bigSepL (fun _ b => byteRange view b 0 (fpBytes state disk (.pool b)))
        (FsState.poolIndices state.superblock.size)) := by
  unfold slotLedger family records dataSlots indirects pools inodes
  simp only [BigSepL.bigSepL_cons.to_eq, BigSepL.bigSepL_append.to_eq,
    BigSepL.bigSepL_flatMap, BigSepL.bigSepL_map]
  simp only [(keys_map _ _).to_eq]
  unfold FsState.poolIndices
  rw [BigSepL.bigSepL_map]
  exact .rfl

theorem record_slots (state : State) disk (bytes : Snapshot.Bytes state disk) :
    bigSepM (M := FsState.InodeMap) (fun i _ => byteRange view
      (fpBlock state (.record i)) (fpOffset (.record i)) (fpBytes state disk (.record i))) state.inodes ⊢
    bigSepM (M := FsState.InodeMap) (fun i n => FsState.recOwned view state.superblock i n.record) state.inodes := by
  apply BigSepM.bigSepM_mono
  intro i n found
  change state.inodes[i]? = some n at found
  simp only [fpBlock, fpOffset, fpBytes, nodeAt_found state i n found]
  rw [← FsState.recOwnedAt_sb view state.superblock i n.record (bytes.inum i n found)]
  exact BIBase.Entails.refl _

theorem data_slots (state : State) disk (bytes : Snapshot.Bytes state disk) :
    bigSepM (M := FsState.InodeMap) (fun i _ =>
      bigSepM (M := FsState.SlotMap) (fun k _ => byteRange view
        (fpBlock state (.data i k)) 0 (fpBytes state disk (.data i k))) (nodeAt state i).blocks) state.inodes ⊢
    bigSepM (M := FsState.InodeMap) (fun _ n =>
      bigSepM (M := FsState.SlotMap) (fun k block => blockOwned view (n.address k) block) n.blocks) state.inodes := by
  apply BigSepM.bigSepM_mono
  intro i n found
  change state.inodes[i]? = some n at found
  simp only [fpBlock, fpBytes, nodeAt_found state i n found]
  apply BigSepM.bigSepM_mono
  intro k block get
  change n.blocks[k]? = some block at get
  simp only [get, Option.getD_some]
  iintro H
  unfold blockOwned
  isplit
  · ipureintro; exact bytes.blockSize _ _ (bytes.data i n k block found get)
  · iexact H

theorem indirect_slots (state : State) disk (bytes : Snapshot.Bytes state disk) :
    bigSepM (M := FsState.InodeMap) (fun i _ => byteRange view
      (fpBlock state (.indirect i)) 0 (fpBytes state disk (.indirect i))) state.inodes ⊢
    bigSepM (M := FsState.InodeMap) (fun _ n => FsState.indOwned view n) state.inodes := by
  apply BigSepM.bigSepM_mono
  intro i n found
  change state.inodes[i]? = some n at found
  simp only [fpBlock, fpBytes, nodeAt_found state i n found, FsState.indOwned, FsState.indOwnedQ]
  by_cases zero : n.indirect = 0
  · simp only [if_pos zero, (byteRange_nil view _ _).to_eq]
    exact BIBase.Entails.refl _
  · simp only [if_neg zero]
    iintro H
    unfold blockOwnedQ
    isplit
    · ipureintro; exact bytes.blockSize _ _ (bytes.indirect i n found zero)
    · iunfold byteRange at H; iexact H

theorem pool_slots (state : State) disk (bytes : Snapshot.Bytes state disk) :
    bigSepL (fun _ b => byteRange view b 0 (fpBytes state disk (.pool b)))
      (FsState.poolIndices state.superblock.size) ⊢
    FsState.freePool view state.superblock.size state.used := by
  unfold FsState.freePool
  apply BigSepL.bigSepL_mono
  intro k b get
  have mem := List.mem_of_getElem? get
  obtain ⟨index, bound, rfl⟩ := List.mem_map.mp mem
  have lt := List.mem_range.mp bound
  have range : 0 ≤ (Int.ofNat index) ∧ (Int.ofNat index) < state.superblock.size := by
    change 0 ≤ (index : Int) ∧ (index : Int) < state.superblock.size
    omega
  unfold FsState.poolElt fpBytes
  by_cases used : (Int.ofNat index) ∈ state.used
  · simp only [if_pos used, (byteRange_nil view _ _).to_eq]
    exact BIBase.Entails.refl _
  · obtain ⟨block, stored⟩ := Option.isSome_iff_exists.mp (bytes.pool _ range used)
    simp only [if_neg used, stored, Option.getD_some]
    iintro H
    iexists block
    unfold blockOwned
    isplit
    · ipureintro; exact bytes.blockSize _ _ stored
    · iexact H

end MachCSL.Logic.FsDurAssemble
