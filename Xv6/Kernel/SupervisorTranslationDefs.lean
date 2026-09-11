import Xv6.Kernel.KptResidueDefs
import Iris.BI.Lib.MonoNat

/-! Source IntrDefs.v §§6b/translation slot and RiscvPtsto.v 591–596.
This is a linear slot containing native register/KPT resources, not a new
Iris invariant or a proof that the hardware has switched translation mode. -/
namespace Xv6.Kernel.SupervisorTranslation
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := KptResidue.Capacity

/-- Reuse the machine's existing mono-nat camera, with an explicit runtime
name; this cannot silently select a second mono-nat capacity. -/
@[reducible] def Capacity.monoNat {GF : BundledGFunctors} (capacity : Capacity GF)
    (name : GName) : MonoNatG GF :=
  ⟨capacity.machine.era.views.sharedNat, name⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def pendingAt (name : GName) : IProp GF :=
  letI := capacity.monoNat name
  MonoNat.auth_own name (.own (1 : Qp).half) (.ofNat 0)
def readyAt (name : GName) : IProp GF :=
  letI := capacity.monoNat name
  MonoNat.auth_own name (.own 1) (.ofNat 0)
def shotAt (name : GName) : IProp GF :=
  letI := capacity.monoNat name
  MonoNat.auth_own name (.own 1) (.ofNat 1)
def onAt (name : GName) : IProp GF :=
  letI := capacity.monoNat name
  MonoNat.lb_own name (.ofNat 1)

abbrev pending (era : Era.Record) (cpu : CPU) := pendingAt capacity (era.supervisorTranslation cpu)
abbrev shot (era : Era.Record) (cpu : CPU) := shotAt capacity (era.supervisorTranslation cpu)
abbrev kptOn (era : Era.Record) (cpu : CPU) := onAt capacity (era.supervisorTranslation cpu)

def BareSatp (satp : BitVec 64) : Prop := _get_Satp64_Mode (Mk_Satp64 satp) = 0#4

/-- Exact SRegime.bare_inv. The TLB cell remains with the client. The root
index zero belongs to the source PMP resource, whose full facts are reused. -/
def bare (era : Era.Record) (cpu : CPU) : IProp GF :=
  iprop(∃ satp : BitVec 64, KptResidue.satpCell capacity era cpu satp ∗
    ⌜BareSatp satp⌝ ∗ KptResidue.pmpConfig capacity era cpu 0#44)

def stvec (era : Era.Record) (cpu : CPU) : IProp GF :=
  iprop(∃ value : BitVec 64,
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .stvec (.own 1) value)

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- Exact source strans_inv, with the KPT namespace explicit. Only the Bare
arm owns stvec; only the KPT residue owns TLB. No arm owns both receipts. -/
noncomputable def slot (era : Era.Record) (cpu : CPU) (N : Namespace) : IProp GF :=
  iprop((pending capacity era cpu ∗ bare capacity era cpu ∗ stvec capacity era cpu) ∨
    (shot capacity era cpu ∗ ∃ root, KptResidue.residue capacity era cpu N root))

/-- The source namespace specialization. -/
noncomputable abbrev sourceSlot (era : Era.Record) (cpu : CPU) : IProp GF :=
  slot capacity era cpu KptGhost.kptN

end Xv6.Kernel.SupervisorTranslation
