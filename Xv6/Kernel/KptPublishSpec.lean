import Xv6.Kernel.KptPublishDefs

namespace Xv6.Kernel.KptPublish
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

structure PureSpec : Prop where
  slot_set_self : ∀ (word : BitVec 64) (j : Nat), nthByte word j ∈ PteCanonical.slotSet word j

/-- The exact physical transformation. Generic drained folds carry an explicit
agent-zero view receipt; the self-contained final gate derives that receipt
only for an agent-zero publisher. Boot forwarding is a separate route. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  pin_word : ∀ era a word B,
    iprop(⊢ viewZero capacity era B -∗
      ContextPinMint.pinnedWord (contextCapacity capacity) (contextNames era)
        a word B (PteCanonical.slotSet word) -∗
      KptOwnership.kernelSlot capacity era B a (.own 1) word)
  slot_view : ∀ era cpu ξ g a (word : BitVec 64),
    ContextPinMint.Drained cpu g →
    iprop(⊢ viewZero capacity era (g.views cpu) -∗
      heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.slotOwn capacity era (.user ξ) a (.own 1) word ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.slotOwn capacity era (.kernel (g.views cpu)) a (.own 1) word)
  slots_view : ∀ era cpu ξ g (α : Type) (indices : List α) (address : α → PhysicalAddress) (word : α → BitVec 64),
    ContextPinMint.Drained cpu g →
    iprop(⊢ viewZero capacity era (g.views cpu) -∗
      heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      slotsOwn capacity era (.user ξ) indices address word ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      slotsOwn capacity era (.kernel (g.views cpu)) indices address word)
  page_view : ∀ era cpu ξ g tree,
    ContextPinMint.Drained cpu g →
    iprop(⊢ viewZero capacity era (g.views cpu) -∗
      heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.pageOwn capacity era (.user ξ) (.own 1) tree ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.pageOwn capacity era (.kernel (g.views cpu)) (.own 1) tree)
  tree_view : ∀ era cpu ξ g (depth : Nat) tree,
    ContextPinMint.Drained cpu g →
    iprop(⊢ viewZero capacity era (g.views cpu) -∗
      heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.treeOwn capacity era (.user ξ) depth (.own 1) tree ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.treeOwn capacity era (.kernel (g.views cpu)) depth (.own 1) tree)
  publish_view : ∀ era cpu ξ g (depth : Nat) tree,
    ContextPinMint.Drained cpu g → hartAgent cpu = 0 →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.treeOwn capacity era (.user ξ) depth (.own 1) tree ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.treeOwn capacity era (.kernel (g.views cpu)) depth (.own 1) tree ∗
      logBound capacity era (g.views cpu) ∗ viewHart capacity era cpu (g.views cpu))
  slot_boot : ∀ era cpu ξ g a (word : BitVec 64),
    hartAgent cpu = 0 →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.slotOwn capacity era (.user ξ) a (.own 1) word ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.slotOwn capacity era (.kernel g.log.length) a (.own 1) word)
  slots_boot : ∀ era cpu ξ g (α : Type) (indices : List α) (address : α → PhysicalAddress) (word : α → BitVec 64),
    hartAgent cpu = 0 →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      slotsOwn capacity era (.user ξ) indices address word ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      slotsOwn capacity era (.kernel g.log.length) indices address word)
  page_boot : ∀ era cpu ξ g tree,
    hartAgent cpu = 0 →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.pageOwn capacity era (.user ξ) (.own 1) tree ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.pageOwn capacity era (.kernel g.log.length) (.own 1) tree)
  tree_boot : ∀ era cpu ξ g (depth : Nat) tree,
    hartAgent cpu = 0 →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.treeOwn capacity era (.user ξ) depth (.own 1) tree ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.treeOwn capacity era (.kernel g.log.length) depth (.own 1) tree)
  publish_boot : ∀ era cpu ξ g (depth : Nat) tree,
    hartAgent cpu = 0 →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.treeOwn capacity era (.user ξ) depth (.own 1) tree ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.treeOwn capacity era (.kernel g.log.length) depth (.own 1) tree ∗
      logBound capacity era g.log.length)

/-- Composition with the existing native shared-invariant allocation. These
consume the supplied map authority and one-shot unset tokens at their existing
names, after physically transforming the user tree. They do not allocate a
replacement machine or assume the desired kernel-tier ownership. -/
structure AllocationSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  allocate_view : ∀ era (N : Namespace) (E : CoPset) cpu ξ g root mapping tree,
    ContextPinMint.Drained cpu g → hartAgent cpu = 0 →
    KptShared.TreeSpec root mapping tree →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.treeOwn capacity era (.user ξ) 2 (.own 1) tree -∗
      KptGhost.mapAuth capacity.ghost era.kernelMap mapping -∗
      KptGhost.unset capacity.ghost era.kernelPageTable -∗
      KptGhost.boundUnset capacity.ghost era.kernelPageTableBound ={E}=∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptShared.shared capacity era N root ∗ KptShared.snapshot capacity era tree ∗
      KptShared.bound capacity era (g.views cpu) ∗ logBound capacity era (g.views cpu) ∗
      KptShared.credentials capacity era cpu ∗ viewHart capacity era cpu (g.views cpu))
  allocate_boot : ∀ era (N : Namespace) (E : CoPset) cpu ξ g root mapping tree,
    hartAgent cpu = 0 →
    KptShared.TreeSpec root mapping tree →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.treeOwn capacity era (.user ξ) 2 (.own 1) tree -∗
      KptGhost.mapAuth capacity.ghost era.kernelMap mapping -∗
      KptGhost.unset capacity.ghost era.kernelPageTable -∗
      KptGhost.boundUnset capacity.ghost era.kernelPageTableBound ={E}=∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptShared.shared capacity era N root ∗ KptShared.snapshot capacity era tree ∗
      KptShared.bound capacity era g.log.length ∗ logBound capacity era g.log.length ∗
      KptShared.credentials capacity era cpu)

end Xv6.Kernel.KptPublish
