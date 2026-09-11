import Xv6.Kernel.KptSharedPureDefs
import Xv6.Kernel.KptOwnershipDefs
import Iris.Instances.Lib.Invariants

noncomputable section
namespace Xv6.Kernel.KptShared
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic

abbrev Capacity := KptOwnership.Capacity

/-- The exact event-address facts derived from owned table slots. -/
def AddressOK (address : PhysicalAddress) : Prop :=
  Tso.AddrIsRAM address ∧ Tso.AddrIsRAM (addressAdd address 7) ∧
    LeanPaperStock.Functions.is_aligned_paddr (.Physaddr address) 8 = true

variable {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)

abbrev snapshot (tree : PtTree.Tree) : IProp GF :=
  KptGhost.snapshot capacity.ghost era.kernelPageTable tree
abbrev bound (B : Nat) : IProp GF :=
  KptGhost.bound capacity.ghost era.kernelPageTableBound era.logLength B
abbrev mapAt (vpn : PtTree.VPN) (ppn : PtTree.PPN) (permission : KptLeaf.Permission) : IProp GF :=
  KptGhost.mapAt capacity.ghost era.kernelMap vpn ppn permission

def body (root : PtTree.PPN) : IProp GF :=
  iprop(∃ tree mapping B,
    KptOwnership.treeOwn capacity era (.kernel B) 2 (.own 1) tree ∗
    snapshot capacity era tree ∗ bound capacity era B ∗
    KptGhost.mapAuth capacity.ghost era.kernelMap mapping ∗ ⌜TreeSpec root mapping tree⌝)

/-- A per-hart credential retains the exact shared bound and either the
hart's view receipt or the source boot-hart forwarding credential. -/
def credentials (cpu : CPU) : IProp GF :=
  iprop(∃ B, bound capacity era B ∗ TsoPinnedReadWP.credential capacity.machine era cpu B)

variable {hlc : HasLC} [InvGS_gen hlc GF]
def shared (N : Namespace) (root : PtTree.PPN) : IProp GF := inv N (body capacity era root)
def kernelShared (root : PtTree.PPN) : IProp GF := shared capacity era KptGhost.kptN root

end Xv6.Kernel.KptShared
