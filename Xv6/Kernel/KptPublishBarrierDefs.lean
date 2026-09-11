import Xv6.Kernel.KptPublishDefs
import MachCSL.Logic.BarrierWPDefs

/-! Physical page-table publication at an actual native barrier event.
The basic event update produces the physical kernel-tier table; shared
invariant allocation is a subsequent fancy update at the same continuation. -/
namespace Xv6.Kernel.KptPublishBarrier
open Iris Iris.BI MachCSL.Machine MachCSL.Logic

abbrev Capacity := KptPublish.Capacity
inductive Route where
  | boot | view

variable {GF : BundledGFunctors} (capacity : Capacity GF)

noncomputable def receipt (era : Era.Record) (cpu : CPU) (B : Nat) : Route → IProp GF
  | .boot => iprop(True)
  | .view => KptPublish.viewHart capacity era cpu B

noncomputable def input (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (mapping : KptGhost.Map) (tree : PtTree.Tree) : IProp GF :=
  iprop(KptPublish.running capacity era cpu ξ ∗
    KptOwnership.treeOwn capacity era (.user ξ) 2 (.own 1) tree ∗
    KptGhost.mapAuth capacity.ghost era.kernelMap mapping ∗
    KptGhost.unset capacity.ghost era.kernelPageTable ∗
    KptGhost.boundUnset capacity.ghost era.kernelPageTableBound)

/-- The bound comes from the actual event state, hidden existentially from
the client. No global-log-top view is inferred on the boot route. -/
noncomputable def published (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (mapping : KptGhost.Map) (tree : PtTree.Tree) (route : Route) : IProp GF :=
  iprop(∃ B, KptPublish.running capacity era cpu ξ ∗
    KptOwnership.treeOwn capacity era (.kernel B) 2 (.own 1) tree ∗
    KptPublish.logBound capacity era B ∗ receipt capacity era cpu B route ∗
    KptGhost.mapAuth capacity.ghost era.kernelMap mapping ∗
    KptGhost.unset capacity.ghost era.kernelPageTable ∗
    KptGhost.boundUnset capacity.ghost era.kernelPageTableBound)

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def output (era : Era.Record) (cpu : CPU) (ξ : TsoContext.CtxId)
    (N : Namespace) (root : PtTree.PPN) (tree : PtTree.Tree) (route : Route) : IProp GF :=
  iprop(∃ B, KptPublish.running capacity era cpu ξ ∗
    KptShared.shared capacity era N root ∗ KptShared.snapshot capacity era tree ∗
    KptShared.bound capacity era B ∗ KptPublish.logBound capacity era B ∗
    KptShared.credentials capacity era cpu ∗ receipt capacity era cpu B route)

end Xv6.Kernel.KptPublishBarrier
