import MachCSL.Logic.FsDurCouplingDefs

namespace MachCSL.Logic.FsDurCoupling
open Iris Iris.Std Iris.BI Xv6.Fs DurableNode DurableState
variable {GF : BundledGFunctors}

structure CouplingSpec (view : FsView.View GF) : Prop where
  disjoint : ∀ sb nodes, FsView.PhiExcl view → FsDurInodeRead.inodeLeg view sb nodes ⊢
    ⌜∀ (i : Int) node (j : Int) other b, nodes[i]? = some node → nodes[j]? = some other → Node.Owns node b → Node.Owns other b → i = j⌝
  used : ∀ sb nodes nb used, FsView.PhiExcl view →
    FsState.freePool view nb used ∗ FsDurInodeRead.inodeLeg view sb nodes ⊢
      ⌜∀ (i : Int) node b, nodes[i]? = some node → Node.Owns node b → 0 ≤ b ∧ b < nb → b ∈ used⌝
  record : ∀ sb nodes (i z : Int) node other b, nodes[i]? = some node → nodes[z]? = some other → Node.Owns node b →
    FsDurInodeRead.inodeLeg view sb nodes ⊢ (∃ bytes, FsView.blockOwned view b bytes) ∗ FsState.recOwned view sb z other.record
  notMetadata : ∀ state, FsView.PhiExcl view →
    (∀ (i : Int) node, state.inodes[i]? = some node → 0 ≤ i ∧ i < 2 ^ 32) →
    (∀ i node, state.inodes[i]? = some node → DurableNode.Local i node) →
    metadataLeg view state ⊢ ⌜∀ (i : Int) node b, state.inodes[i]? = some node → Node.Owns node b → ¬Metadata state b⌝
  metadataUsed : ∀ state, FsView.PhiExcl view →
    (∀ (i : Int) node, state.inodes[i]? = some node → 0 ≤ i ∧ i < 2 ^ 32) →
    (∀ i node, state.inodes[i]? = some node → DurableNode.Local i node) →
    metadataLeg view state ∗ FsState.freePool view state.superblock.size state.used ⊢
      ⌜∀ b, Metadata state b → 0 ≤ b ∧ b < state.superblock.size → b ∈ state.used⌝

end MachCSL.Logic.FsDurCoupling
