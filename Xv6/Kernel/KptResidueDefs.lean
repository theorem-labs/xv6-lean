import Xv6.Kernel.KptSharedDefs
import Xv6.Kernel.TlbCoherenceDefs
import MachCSL.Logic.SupervisorPmpDefs

/-! Source KptShare.v per-hart translation residue. It owns the actual full
SATP/TLB cells and exact source PMP resource, without a CSR transition claim. -/
namespace Xv6.Kernel.KptResidue
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KptShared.Capacity
abbrev Tlb := TlbCoherence.Tlb

/-- The source's three SATP facts, using actual generated 64-bit accessors. -/
def SatpRooted (root : PtTree.PPN) (satp : BitVec 64) : Prop :=
  _get_Satp64_Mode (Mk_Satp64 satp) = 8#4 ∧
    (satp_to_asid (k_n := 64) satp).zeroExtend 16 = 0#16 ∧
    satp_to_ppn (k_n := 64) satp = root

/-- All physical TLB slots are empty; no hash-injectivity assumption. -/
def EmptyTlb (tlb : Tlb) : Prop := ∀ i : Fin 64, tlb[i.val]? = some none

variable {GF : BundledGFunctors} (capacity : Capacity GF) (era : Era.Record)

def tlbSnapOK (tlb : Tlb) : IProp GF :=
  iprop(∃ tree, ⌜TlbCoherence.Coherent 0#16 tree tlb⌝ ∗ KptShared.snapshot capacity era tree)

abbrev credentials (cpu : CPU) : IProp GF := KptShared.credentials capacity era cpu

abbrev satpCell (cpu : CPU) (satp : BitVec 64) : IProp GF :=
  Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .satp (.own 1) satp
abbrev tlbCell (cpu : CPU) (tlb : Tlb) : IProp GF :=
  Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .tlb (.own 1) tlb

/-- Reuse all six source PMP facts and both full vector cells. In particular,
this is not the weaker fact that a particular read is granted. -/
abbrev pmpConfig (cpu : CPU) (root : PtTree.PPN) : IProp GF :=
  MachCSL.Logic.SupervisorPmp.config capacity.machine.era.registers (era.registers cpu) root

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- The open representation exposes every source conjunct; it adds no
operational invariant or extra register authority. -/
noncomputable def parts (cpu : CPU) (N : Namespace) (root : PtTree.PPN)
    (satp : BitVec 64) (tlb : Tlb) : IProp GF :=
  iprop(satpCell capacity era cpu satp ∗ ⌜SatpRooted root satp⌝ ∗
    tlbCell capacity era cpu tlb ∗ tlbSnapOK capacity era tlb ∗ pmpConfig capacity era cpu root ∗
    KptShared.shared capacity era N root ∗ credentials capacity era cpu)

noncomputable def residue (cpu : CPU) (N : Namespace) (root : PtTree.PPN) : IProp GF :=
  iprop(∃ satp tlb, parts capacity era cpu N root satp tlb)

end Xv6.Kernel.KptResidue
