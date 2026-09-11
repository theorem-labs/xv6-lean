import MachCSL.Logic.FsDurCouplingProofs

namespace MachCSL.Logic.FsDurCoupling
open Iris Iris.Std Iris.BI Xv6.Fs DurableNode DurableState
open FsDurInodeRead
variable {GF : BundledGFunctors} (view : FsView.View GF)

theorem fs_owns_not_meta (exclusive : FsView.PhiExcl view) (state : State)
    (bounds : ∀ (i : Int) node, state.inodes[i]? = some node → 0 ≤ i ∧ i < 2 ^ 32)
    (locals : ∀ i node, state.inodes[i]? = some node → DurableNode.Local i node) :
    metadataLeg view state ⊢
      ⌜∀ (i : Int) node b, state.inodes[i]? = some node → Node.Owns node b → ¬Metadata state b⌝ := by
  unfold metadataLeg
  iintro ⟨Hs, Hb, Hin⟩
  iapply pure_forall.mpr
  iintro %i
  iapply pure_forall.mpr
  iintro %node
  iapply pure_forall.mpr
  iintro %b
  iapply pure_imp.mpr
  iintro %found
  iapply pure_imp.mpr
  iintro %owns
  iapply pure_imp.mpr
  iintro %isMetadata
  rcases isMetadata with rfl | rfl | ⟨z, present, rfl⟩
  · unfold inodeLeg
    ihave Hi := BigSepM.bigSepM_lookup (M := FsState.InodeMap) found $$ Hin
    ihave ⟨%bytes, Howned⟩ := inode_phi_owns view state.superblock i node 1 owns $$ Hi
    ihave Hfalse := FsView.blockOwned_excl view exclusive 1 state.superblockBytes bytes $$ Hs Howned
    icases Hfalse with ⟨⟩
  · unfold inodeLeg
    ihave Hi := BigSepM.bigSepM_lookup (M := FsState.InodeMap) found $$ Hin
    ihave ⟨%bytes, Howned⟩ := inode_phi_owns view state.superblock i node state.superblock.bmapstart owns $$ Hi
    ihave Hfalse := FsView.blockOwned_excl view exclusive state.superblock.bmapstart
      (BitmapEncoding.bitmapBytes 1024 state.used) bytes $$ Hb Howned
    icases Hfalse with ⟨⟩
  · obtain ⟨other, getZ⟩ := Option.isSome_iff_exists.mp present
    ihave ⟨⟨%bytes, Howned⟩, Hr⟩ := inodes_owns_and_rec view state.superblock state.inodes i z node other
      (state.superblock.inodestart + z / 16) found getZ owns $$ Hin
    rw [← FsState.recOwnedAt_sb view state.superblock z other.record (bounds z other getZ)]
    unfold FsState.recOwnedAt FsState.recOwnedAtQ
    have len := dinodeBytes_length other.record (locals z other getZ).record
    have modbound : 0 ≤ z % 16 ∧ z % 16 < 16 :=
      ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
    ihave Howned := (BIBase.BiEntails.of_eq (FsView.blockOwned_one view _ bytes)).mp $$ Howned
    iapply FsDurRead.blk_run_overlap view exclusive (.own 1) (.own 1)
      (state.superblock.inodestart + z / 16) (64 * (z % 16)) bytes (dinodeBytes other.record)
      (FsView.dfrac_full_invalid _) (by omega) (by omega) (by omega) $$ [$Howned $Hr]

theorem fs_meta_used (exclusive : FsView.PhiExcl view) (state : State)
    (bounds : ∀ (i : Int) node, state.inodes[i]? = some node → 0 ≤ i ∧ i < 2 ^ 32)
    (locals : ∀ i node, state.inodes[i]? = some node → DurableNode.Local i node) :
    metadataLeg view state ∗ FsState.freePool view state.superblock.size state.used ⊢
      ⌜∀ b, Metadata state b → 0 ≤ b ∧ b < state.superblock.size → b ∈ state.used⌝ := by
  unfold metadataLeg
  iintro ⟨⟨Hs, Hb, Hin⟩, Hp⟩
  iapply pure_forall.mpr
  iintro %b
  iapply pure_imp.mpr
  iintro %isMetadata
  iapply pure_imp.mpr
  iintro %bound
  rcases isMetadata with rfl | rfl | ⟨z, present, rfl⟩
  · ihave Hs := (BIBase.BiEntails.of_eq (FsView.blockOwned_one view 1 state.superblockBytes)).mp $$ Hs
    iapply FsState.freePool_usedQ view exclusive (.own 1) state.superblock.size state.used 1 state.superblockBytes bound $$ Hp Hs
  · ihave Hb := (BIBase.BiEntails.of_eq (FsView.blockOwned_one view state.superblock.bmapstart
      (BitmapEncoding.bitmapBytes 1024 state.used))).mp $$ Hb
    iapply FsState.freePool_usedQ view exclusive (.own 1) state.superblock.size state.used state.superblock.bmapstart
      (BitmapEncoding.bitmapBytes 1024 state.used) bound $$ Hp Hb
  · obtain ⟨other, found⟩ := Option.isSome_iff_exists.mp present
    unfold inodeLeg
    ihave Hi := BigSepM.bigSepM_lookup (M := FsState.InodeMap) found $$ Hin
    unfold FsState.inodePhi
    icases Hi with ⟨Hr, _⟩
    rw [← FsState.recOwnedAt_sb view state.superblock z other.record (bounds z other found)]
    unfold FsState.recOwnedAt FsState.recOwnedAtQ
    have len := dinodeBytes_length other.record (locals z other found).record
    have modbound : 0 ≤ z % 16 ∧ z % 16 < 16 :=
      ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
    have use := FsDurRead.free_pool_used_run view exclusive state.superblock.size state.used
      (state.superblock.inodestart + z / 16) (64 * (z % 16)) (dinodeBytes other.record)
      bound (by omega) (by omega) (by omega)
    rw [FsView.byteRange_one] at use
    iapply use $$ [$Hp $Hr]

theorem couplingSpec : CouplingSpec view where
  disjoint sb nodes exclusive := fs_inodes_phi_disj view exclusive sb nodes
  used sb nodes nb used exclusive := fs_inodes_phi_used view exclusive sb nodes nb used
  record := inodes_owns_and_rec view
  notMetadata state exclusive := fs_owns_not_meta view exclusive state
  metadataUsed state exclusive := fs_meta_used view exclusive state

end MachCSL.Logic.FsDurCoupling
