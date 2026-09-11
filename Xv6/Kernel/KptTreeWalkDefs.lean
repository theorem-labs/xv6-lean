import Xv6.Kernel.KptReadEventDefs
import Xv6.Kernel.Sv39TreeWalkDefs

/-! Shared KPT counterpart of the actual three-level Sv39 walk. The inert
snapshot fixes raw upper pointers; native shared events choose each read. -/
namespace Xv6.Kernel.KptTreeWalk
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KptShared.Capacity
abbrev Shares := Sv39TreeWalk.Shares
abbrev Result := Sv39TreeWalk.Result
abbrev Config := Sv39TreeWalk.Config
abbrev program := Sv39TreeWalk.program
abbrev output := Sv39TreeWalk.output

abbrev cells {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)
    (cpu : CPU) (rs : RegisterFile) (shares : Shares) : IProp GF :=
  SupervisorPteRead.cells capacity.machine era cpu rs shares

abbrev receipts {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)
    (cpu : CPU) (view2 view1 view0 : Nat) : IProp GF :=
  Sv39TreeWalk.receipts capacity.machine era cpu view2 view1 view0

/-- Persistent clients only: physical table slots are obtained and restored
inside the existing shared event implementation, separately at each read. -/
noncomputable def clients {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) (era : Era.Record) (cpu : CPU) (N : Namespace)
    (root : PtTree.PPN) (tree : PtTree.Tree) (bound : Nat) : IProp GF :=
  iprop(KptShared.shared capacity era N root ∗ KptShared.snapshot capacity era tree ∗
    KptShared.bound capacity era bound ∗ TsoPinnedReadWP.credential capacity.machine era cpu bound)

end Xv6.Kernel.KptTreeWalk
