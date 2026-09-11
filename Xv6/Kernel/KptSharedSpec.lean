import Xv6.Kernel.KptSharedDefs

namespace Xv6.Kernel.KptShared
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

/-- Native publication consumes an already pinned physical tree. Access
opens and closes the same invariant within one fancy update. -/
structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  body_timeless : ∀ era root, Timeless (body capacity era root)
  allocate : ∀ era (N : Namespace) (E : CoPset) root mapping tree B,
    TreeSpec root mapping tree →
    iprop(⊢ KptOwnership.treeOwn capacity era (.kernel B) 2 (.own 1) tree -∗
      KptGhost.mapAuth capacity.ghost era.kernelMap mapping -∗
      Tso.Views.llb capacity.machine.era.views era.logLength B -∗
      KptGhost.unset capacity.ghost era.kernelPageTable -∗
      KptGhost.boundUnset capacity.ghost era.kernelPageTableBound ={E}=∗
      shared capacity era N root ∗ snapshot capacity era tree ∗ bound capacity era B)
  read_snapshot : ∀ era (N : Namespace) (E : CoPset) root,
    (↑N : CoPset) ⊆ E →
    iprop(⊢ shared capacity era N root ={E}=∗ ∃ tree, snapshot capacity era tree)
  read_path : ∀ era (N : Namespace) (E : CoPset) root tree vpn ppn permission,
    (↑N : CoPset) ⊆ E →
    iprop(⊢ shared capacity era N root -∗ snapshot capacity era tree -∗
      mapAt capacity era vpn ppn permission ={E}=∗
      ⌜PtTree.base tree = root ∧ ∃ p2 p1 a d,
        PtTree.Maps tree vpn p2 p1 (KptLeaf.word ppn permission a d) ∧
        AddressOK (PtTree.addr2 tree vpn) ∧ AddressOK (PtTree.addr1 p2 vpn) ∧
        AddressOK (PtTree.addr0 p1 vpn)⌝)

end Xv6.Kernel.KptShared
