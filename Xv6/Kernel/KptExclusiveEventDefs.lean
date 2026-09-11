import Xv6.Kernel.KptSharedDefs
import MachCSL.Logic.MemoryExclusiveWPDefs

/-! The actual exclusive eight-byte leaf event. Its successful value is
selected from current physical memory inside the shared invariant access. -/
namespace Xv6.Kernel.KptExclusiveEvent
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := KptShared.Capacity

def ReadFact (reference word : PtTree.Word) : Prop :=
  PteCanonical.canon word = PteCanonical.canon reference

/-- Both resources are persistent native clients of the same publication. -/
noncomputable def clients {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) (era : Era.Record) (N : Namespace)
    (root : PtTree.PPN) (tree : PtTree.Tree) : IProp GF :=
  iprop(KptShared.shared capacity era N root ∗ KptShared.snapshot capacity era tree)

end Xv6.Kernel.KptExclusiveEvent
