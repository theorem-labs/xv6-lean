import MachCSL.Logic.FsDurCouplingSpec
import MachCSL.Logic.FsDurInodeReadSlotProofs

namespace MachCSL.Logic.FsDurCoupling
open Iris Iris.Std Iris.BI Xv6.Fs DurableNode DurableState
open FsDurInodeRead
variable {GF : BundledGFunctors} (view : FsView.View GF)

theorem fs_inodes_phi_disj (exclusive : FsView.PhiExcl view) sb nodes :
    inodeLeg view sb nodes ⊢
      ⌜∀ (i : Int) node (j : Int) other b, nodes[i]? = some node → nodes[j]? = some other → Node.Owns node b → Node.Owns other b → i = j⌝ := by
  iintro Hin
  iapply pure_forall.mpr
  iintro %i
  iapply pure_forall.mpr
  iintro %node
  iapply pure_forall.mpr
  iintro %j
  iapply pure_forall.mpr
  iintro %other
  iapply pure_forall.mpr
  iintro %b
  iapply pure_imp.mpr
  iintro %getI
  iapply pure_imp.mpr
  iintro %getJ
  iapply pure_imp.mpr
  iintro %ownsI
  iapply pure_imp.mpr
  iintro %ownsJ
  by_cases same : i = j
  · ipureintro; exact same
  · unfold inodeLeg
    ihave ⟨Hi, Hrest⟩ := (BigSepM.bigSepM_delete (M := FsState.InodeMap) getI).mp $$ Hin
    have remaining : get? (PartialMap.delete (M := FsState.InodeMap) nodes i) j = some other := by
      rw [get?_delete_ne same]
      exact getJ
    ihave Hj := BigSepM.bigSepM_lookup (M := FsState.InodeMap) remaining $$ Hrest
    ihave ⟨%bytes, Hb⟩ := inode_phi_owns view sb i node b ownsI $$ Hi
    ihave ⟨%bytes', Hb'⟩ := inode_phi_owns view sb j other b ownsJ $$ Hj
    ihave Hfalse := FsView.blockOwned_excl view exclusive b bytes bytes' $$ Hb Hb'
    icases Hfalse with ⟨⟩

theorem fs_inodes_phi_used (exclusive : FsView.PhiExcl view) sb nodes nb used :
    FsState.freePool view nb used ∗ inodeLeg view sb nodes ⊢
      ⌜∀ (i : Int) node b, nodes[i]? = some node → Node.Owns node b → 0 ≤ b ∧ b < nb → b ∈ used⌝ := by
  iintro ⟨Hp, Hin⟩
  iapply pure_forall.mpr
  iintro %i
  iapply pure_forall.mpr
  iintro %node
  iapply pure_forall.mpr
  iintro %b
  iapply pure_imp.mpr
  iintro %getI
  iapply pure_imp.mpr
  iintro %owns
  iapply pure_imp.mpr
  iintro %bound
  unfold inodeLeg
  ihave Hi := BigSepM.bigSepM_lookup (M := FsState.InodeMap) getI $$ Hin
  ihave ⟨%bytes, Hb⟩ := inode_phi_owns view sb i node b owns $$ Hi
  ihave Hb := (BIBase.BiEntails.of_eq (FsView.blockOwned_one view b bytes)).mp $$ Hb
  iapply FsState.freePool_usedQ view exclusive (.own 1) nb used b bytes bound $$ Hp Hb

theorem inodes_owns_and_rec sb nodes (i z : Int) node other b
    (getI : nodes[i]? = some node) (getZ : nodes[z]? = some other) (owns : Node.Owns node b) :
    inodeLeg view sb nodes ⊢ (∃ bytes, FsView.blockOwned view b bytes) ∗ FsState.recOwned view sb z other.record := by
  unfold inodeLeg
  iintro Hin
  by_cases same : i = z
  · subst z
    have equal : other = node := Option.some.inj (getZ.symm.trans getI)
    subst other
    ihave Hi := BigSepM.bigSepM_lookup (M := FsState.InodeMap) getI $$ Hin
    unfold FsState.inodePhi
    icases Hi with ⟨Hr, Hd⟩
    isplitl [Hd]
    · iapply inode_dat_owns view node b owns $$ Hd
    · iexact Hr
  · ihave ⟨Hi, Hrest⟩ := (BigSepM.bigSepM_delete (M := FsState.InodeMap) getI).mp $$ Hin
    have remaining : get? (PartialMap.delete (M := FsState.InodeMap) nodes i) z = some other := by
      rw [get?_delete_ne same]
      exact getZ
    ihave Hz := BigSepM.bigSepM_lookup (M := FsState.InodeMap) remaining $$ Hrest
    ihave Hb := inode_phi_owns view sb i node b owns $$ Hi
    unfold FsState.inodePhi
    icases Hz with ⟨Hr, _⟩
    iframe Hb Hr

end MachCSL.Logic.FsDurCoupling
