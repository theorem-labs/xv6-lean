import Xv6.Kernel.KptSharedDefs
import MachCSL.Logic.MemoryWriteWPDefs

/-! A conditional leaf write changes only the A/D variant represented by
the shared canonical tree. The complete Sail request remains explicit. -/
namespace Xv6.Kernel.KptWriteEvent
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := KptShared.Capacity

noncomputable def clients {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) (era : Era.Record) (N : Namespace)
    (root : PtTree.PPN) (tree : PtTree.Tree) : IProp GF :=
  iprop(KptShared.shared capacity era N root ∗ KptShared.snapshot capacity era tree)

end Xv6.Kernel.KptWriteEvent
