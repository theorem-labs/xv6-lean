import Xv6.Kernel.KptPublishTreeProofs
import Xv6.Kernel.KptSharedLink

namespace Xv6.Kernel.KptPublish
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem publish_view : ∀ era cpu ξ g (depth : Nat) tree,
    ContextPinMint.Drained cpu g → hartAgent cpu = 0 →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.treeOwn capacity era (.user ξ) depth (.own 1) tree ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.treeOwn capacity era (.kernel (g.views cpu)) depth (.own 1) tree ∗
      logBound capacity era (g.views cpu) ∗ viewHart capacity era cpu (g.views cpu)) := by
  intro era cpu ξ g depth tree drained boot
  iintro Hheap Htso Hrun Htree
  have now : iprop(⊢ tsoAt capacity era g -∗ tsoAt capacity era g ∗
      viewHart capacity era cpu (g.views cpu) ∗ logBound capacity era (g.views cpu)) :=
    ContextPinMint.view_now (contextCapacity capacity) (contextNames era) era.imageBytes g cpu
  ihave ⟨Htso, #Hview, #Hlog⟩ := now $$ Htso
  ihave #Hzero : viewZero capacity era (g.views cpu) $$ []
  · unfold viewZero
    rw [← boot]
    iexact Hview
  imod tree_view capacity era cpu ξ g depth tree drained $$ Hzero Hheap Htso Hrun Htree
    with ⟨Hheap, Htso, Hrun, Htree⟩
  imodintro
  iframe Hheap Htso Hrun Htree Hlog Hview

theorem publish_boot : ∀ era cpu ξ g (depth : Nat) tree,
    hartAgent cpu = 0 →
    iprop(⊢ heapAt capacity era g -∗ tsoAt capacity era g -∗
      running capacity era cpu ξ -∗
      KptOwnership.treeOwn capacity era (.user ξ) depth (.own 1) tree ==∗
      heapAt capacity era g ∗ tsoAt capacity era g ∗ running capacity era cpu ξ ∗
      KptOwnership.treeOwn capacity era (.kernel g.log.length) depth (.own 1) tree ∗
      logBound capacity era g.log.length) := by
  intro era cpu ξ g depth tree boot
  iintro Hheap Htso Hrun Htree
  have now : iprop(⊢ tsoAt capacity era g -∗ tsoAt capacity era g ∗ logBound capacity era g.log.length) :=
    ContextPinMint.log_now (contextCapacity capacity) (contextNames era) era.imageBytes g
  ihave ⟨Htso, #Hlog⟩ := now $$ Htso
  imod tree_boot capacity era cpu ξ g depth tree boot $$ Hheap Htso Hrun Htree
    with ⟨Hheap, Htso, Hrun, Htree⟩
  imodintro
  iframe Hheap Htso Hrun Htree Hlog

variable {hlc : HasLC} [InvGS_gen hlc GF]

theorem allocate_view : ∀ era (N : Namespace) (E : CoPset) cpu ξ g root mapping tree,
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
      KptShared.credentials capacity era cpu ∗ viewHart capacity era cpu (g.views cpu)) := by
  intro era N E cpu ξ g root mapping tree drained boot spec
  iintro Hheap Htso Hrun Htree Hmap Hunset HboundUnset
  imod publish_view capacity era cpu ξ g 2 tree drained boot
    $$ Hheap Htso Hrun Htree with ⟨Hheap, Htso, Hrun, Htree, #Hlog, #Hview⟩
  imod (KptShared.nativeSpec capacity).allocate era N E root mapping tree (g.views cpu) spec
    $$ Htree Hmap Hlog Hunset HboundUnset with ⟨#Hshared, #Hsnapshot, #Hbound⟩
  imodintro
  iframe Hheap Htso Hrun Hshared Hsnapshot Hbound Hlog Hview
  unfold KptShared.credentials
  iexists (g.views cpu)
  iframe Hbound
  have cred : iprop(⊢ viewHart capacity era cpu (g.views cpu) -∗
      TsoPinnedReadWP.credential capacity.machine era cpu (g.views cpu)) :=
    TsoPinnedRead.bootCredential_view capacity.machine.era.tso era.tsoNames cpu (g.views cpu)
  iapply cred $$ Hview

theorem allocate_boot : ∀ era (N : Namespace) (E : CoPset) cpu ξ g root mapping tree,
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
      KptShared.credentials capacity era cpu) := by
  intro era N E cpu ξ g root mapping tree boot spec
  iintro Hheap Htso Hrun Htree Hmap Hunset HboundUnset
  imod publish_boot capacity era cpu ξ g 2 tree boot
    $$ Hheap Htso Hrun Htree with ⟨Hheap, Htso, Hrun, Htree, #Hlog⟩
  imod (KptShared.nativeSpec capacity).allocate era N E root mapping tree g.log.length spec
    $$ Htree Hmap Hlog Hunset HboundUnset with ⟨#Hshared, #Hsnapshot, #Hbound⟩
  imodintro
  iframe Hheap Htso Hrun Hshared Hsnapshot Hbound Hlog
  unfold KptShared.credentials
  iexists g.log.length
  iframe Hbound
  have cred : iprop(⊢ logBound capacity era g.log.length -∗
      TsoPinnedReadWP.credential capacity.machine era cpu g.log.length) :=
    TsoPinnedRead.bootCredential_boot capacity.machine.era.tso era.tsoNames cpu g.log.length boot
  iapply cred $$ Hlog

end Xv6.Kernel.KptPublish
