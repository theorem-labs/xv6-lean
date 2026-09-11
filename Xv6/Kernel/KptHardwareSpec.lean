import Xv6.Kernel.KptHardwareDefs

namespace Xv6.Kernel.KptHardware
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  range : ∀ a, KptShared.AddressOK a → SupervisorPhysical.RamRange a 8
  read : ∀ rs a, Controls rs → KptShared.AddressOK a → SupervisorPteRead.Config rs a ramRegion
  write : ∀ rs a, Controls rs → KptShared.AddressOK a → SupervisorPteWrite.Config rs a ramRegion
  path : ∀ rs tree vpn p2 p1, Controls rs →
    KptShared.AddressOK (PtTree.addr2 tree vpn) → KptShared.AddressOK (PtTree.addr1 p2 vpn) →
    KptShared.AddressOK (PtTree.addr0 p1 vpn) → KptMiss.Config rs tree vpn p2 p1 regions

/-- Maps and every address-specific hardware condition are derived from
native mapping/snapshot ownership; only ambient hardware controls are input. -/
structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  mapped : ∀ rs, Controls rs → ∀ era (N : Namespace) (E : CoPset) root tree vpn ppn permission,
    (↑N : CoPset) ⊆ E →
    iprop(⊢ KptShared.shared capacity era N root -∗ KptShared.snapshot capacity era tree -∗
      KptShared.mapAt capacity era vpn ppn permission ={E}=∗
      ⌜PtTree.base tree = root ∧ ∃ p2 p1 a d,
        PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission a d) ∧
        KptMiss.Config rs tree vpn p2 p1 regions⌝)

end Xv6.Kernel.KptHardware
