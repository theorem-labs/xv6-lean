import MachCSL.Logic.FsDurInodeReadSpec
import MachCSL.Logic.FsDurReadOverlapProofs
import MachCSL.Logic.FsStateInodeProofs
import Xv6.Fs.DurableNodeProofs

namespace MachCSL.Logic.FsDurInodeRead
open Iris Iris.Std Iris.BI Xv6.Fs DurableNode DurableState
variable {GF : BundledGFunctors} (view : FsView.View GF)

theorem inode_dat_owns (node : Node) block (owns : node.Owns block) :
    FsState.inodeDat view node ⊢ ∃ bytes, FsView.blockOwned view block bytes := by
  unfold FsState.inodeDat FsState.inodeDatQ
  iintro ⟨Hd, Hi⟩
  rcases owns with ⟨k, present, rfl⟩ | ⟨nonzero, rfl⟩
  · obtain ⟨bytes, found⟩ := Option.isSome_iff_exists.mp present
    ihave Hb := BigSepM.bigSepM_lookup (M := FsState.SlotMap) found $$ Hd
    iexists bytes
    rw [FsView.blockOwned_one]
    iexact Hb
  · unfold FsState.indOwnedQ
    rw [if_neg nonzero]
    iexists indirectBytes node.entries
    rw [FsView.blockOwned_one]
    iexact Hi

theorem inode_phi_owns sb i (node : Node) block (owns : node.Owns block) :
    FsState.inodePhi view sb i node ⊢ ∃ bytes, FsView.blockOwned view block bytes := by
  unfold FsState.inodePhi
  iintro ⟨_, Hd⟩
  iapply inode_dat_owns view node block owns $$ Hd

/-- Distinct stored data slots require separately owned blocks. -/
theorem data_slots_ne (exclusive : FsView.PhiExcl view) (node : Node) k j left right
    (getLeft : node.blocks[k]? = some left) (getRight : node.blocks[j]? = some right) (different : k ≠ j) :
    dataLeg view node ⊢ ⌜node.address k ≠ node.address j⌝ := by
  unfold dataLeg
  iintro H
  ihave ⟨Hl, Hrest⟩ := (BigSepM.bigSepM_delete (M := FsState.SlotMap) getLeft).mp $$ H
  have remaining : get? (PartialMap.delete (M := FsState.SlotMap) node.blocks k) j = some right := by
    rw [get?_delete_ne different]
    exact getRight
  ihave Hr := BigSepM.bigSepM_lookup (M := FsState.SlotMap) remaining $$ Hrest
  iapply FsView.blockOwned_ne view exclusive (node.address k) (node.address j) left right $$ Hl Hr

/-- A stored data slot and the indirect-root leg are different conjuncts. -/
theorem data_indirect_ne (exclusive : FsView.PhiExcl view) (node : Node) k bytes
    (found : node.blocks[k]? = some bytes) (nonzero : node.indirect ≠ 0) :
    FsState.inodeDat view node ⊢ ⌜node.address k ≠ node.indirect⌝ := by
  unfold FsState.inodeDat FsState.inodeDatQ FsState.indOwnedQ
  rw [if_neg nonzero]
  iintro ⟨Hd, Hi⟩
  ihave Hb := BigSepM.bigSepM_lookup (M := FsState.SlotMap) found $$ Hd
  iapply FsView.blockOwnedQ_ne view exclusive (.own 1) (.own 1) (node.address k) node.indirect bytes
    (indirectBytes node.entries) (FsView.dfrac_full_invalid _) $$ Hb Hi

theorem inode_dat_slot_inj (exclusive : FsView.PhiExcl view) i (node : Node)
    (hlocal : DurableNode.Local i node) :
    FsState.inodeDat view node ⊢ ⌜node.SlotInjective⌝ := by
  iintro H
  unfold Node.SlotInjective
  iapply pure_forall.mpr
  iintro %k
  iapply pure_forall.mpr
  iintro %j
  iapply pure_imp.mpr
  iintro %hk
  iapply pure_imp.mpr
  iintro %hj
  iapply pure_imp.mpr
  iintro %nonzero
  iapply pure_imp.mpr
  iintro %same
  by_cases equal : k = j
  · ipureintro; exact equal
  by_cases ki : k = 268
  · subst k
    have jdata : j < 268 := by omega
    rw [slot_indirect, slot_data node j jdata] at same
    rw [slot_indirect] at nonzero
    have present := (hlocal.domain j jdata).mpr (show node.address j ≠ 0 by omega)
    obtain ⟨bytes, found⟩ := Option.isSome_iff_exists.mp present
    ihave %ne := data_indirect_ne view exclusive node j bytes found nonzero $$ H
    ipureintro
    exact False.elim (ne same.symm)
  · have kdata : k < 268 := by omega
    rw [slot_data node k kdata] at nonzero same
    have present := (hlocal.domain k kdata).mpr nonzero
    obtain ⟨bytes, found⟩ := Option.isSome_iff_exists.mp present
    by_cases ji : j = 268
    · subst j
      rw [slot_indirect] at same
      ihave %ne := data_indirect_ne view exclusive node k bytes found (by omega) $$ H
      ipureintro
      exact False.elim (ne same)
    · have jdata : j < 268 := by omega
      rw [slot_data node j jdata] at same
      have present := (hlocal.domain j jdata).mpr (show node.address j ≠ 0 by omega)
      obtain ⟨other, foundOther⟩ := Option.isSome_iff_exists.mp present
      unfold FsState.inodeDat FsState.inodeDatQ
      icases H with ⟨Hd, _⟩
      have use := data_slots_ne view exclusive node k j bytes other found foundOther equal
      simp only [dataLeg, FsView.blockOwned_one] at use
      ihave %ne := use $$ Hd
      ipureintro
      exact False.elim (ne same)

theorem ownershipSpec : OwnershipSpec view where
  owns := inode_dat_owns view
  injective i node exclusive := inode_dat_slot_inj view exclusive i node

end MachCSL.Logic.FsDurInodeRead
