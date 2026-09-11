import Xv6.Kernel.MycpuOffDefs
import Xv6.Kernel.KptResidueDefs
import Xv6.Kernel.KernelStackDefs
import MachCSL.Logic.TimerCapDefs

/-! Regime-independent cycle ownership. The translation cases are the exact
physical `bare_inv` and shared KPT residue components. They are not the
one-shot-indexed `strans_inv`, nor is this packet full `sie_cap_gpr`. -/
namespace Xv6.Kernel.MycpuRegimeShell
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

structure Capacity (GF : BundledGFunctors) where
  translation : KptResidue.Capacity GF
  bits : GhostVarG GF (BitVec 1)

abbrev Capacity.machine {GF : BundledGFunctors} (c : Capacity GF) := c.translation.machine
def Capacity.supervisorBits {GF : BundledGFunctors} (c : Capacity GF) :
    SupervisorBits.Capacity GF := ⟨c.machine.era.registers, c.bits⟩

inductive Regime where
  | bare
  | kpt (namespace_ : Namespace) (root : PtTree.PPN)

/-- The physical Bare resource admits identity-tier words only. This pure
index restriction is not the missing source publication receipt. -/
def Admits : Regime → KernelDatum.Tier → Prop
  | .bare, .identity => True
  | .bare, .full => False
  | .kpt _ _, _ => True

/-- Exactly the nine control shares outside pc_is, mstatus and the GPRs.
No translation register appears here. -/
structure Shares where
  privilege : DFrac
  misa : DFrac
  enable : DFrac
  delegation : DFrac
  environment : DFrac
  landing : DFrac
  pma : DFrac
  htif : DFrac
  hart : DFrac

/-- Source sconf/hw shares for these exposed components. The other hw_config
cells and mapping claims remain separately owned prerequisites. -/
def sourceShares : Shares :=
  ⟨.own 1, .discard, .own 1, .own 1, .own 1, .discard, .discard, .discard, .own 1⟩

def controlFootprint (s : Shares) : RegisterFootprint.Footprint :=
  SupervisorRetirement.pcFootprint ++
    [(.cur_privilege, s.privilege), (.misa, s.misa), (.mie, s.enable),
     (.mideleg, s.delegation), (.menvcfg, s.environment), (.elp, s.landing),
     (.pma_regions, s.pma), (.htif_tohost_base, s.htif), (.hart_state, s.hart)]

def gprFootprint : RegisterFootprint.Footprint := HartTp.physicalKeys.map (fun r => (r, .own 1))
def footprint (s : Shares) : RegisterFootprint.Footprint :=
  controlFootprint s ++ [(.mstatus, .own 1)] ++ gprFootprint

abbrev entry := MycpuOff.entry
abbrev started := MycpuCycleShell.started
abbrev Completed := MycpuCycleShell.completed
abbrev finish [Platform] (tick : Bool) (step : _root_.Step) : SailM Unit :=
  MycpuCycleShell.finish tick step

def active [Platform] (tick : Bool) : SailM Unit := run_hart_active 0 >>= finish tick

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- SRegime.v:833–838. In particular this owns no TLB cell. -/
def bare (era : Era.Record) (cpu : CPU) : IProp GF :=
  iprop(∃ satp : BitVec 64,
    Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .satp (.own 1) satp ∗
    ⌜_get_Satp64_Mode (Mk_Satp64 satp) = 0#4⌝ ∗
    MachCSL.Logic.SupervisorPmp.config capacity.machine.era.registers (era.registers cpu) 0#44)

def controls (era : Era.Record) (cpu : CPU) (control : RegisterFile) (shares : Shares) : IProp GF :=
  RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) control (controlFootprint shares)

def bitFrame (era : Era.Record) (cpu : CPU) (ms : BitVec 64) : IProp GF :=
  iprop(SupervisorBits.bit capacity.supervisorBits (SupervisorBits.namesOfEra era cpu).sie
      SupervisorBits.half (_get_Mstatus_SIE ms) ∗
    SupervisorBits.sretTie capacity.supervisorBits (SupervisorBits.namesOfEra era cpu) ms ∗
    ⌜SupervisorBits.MsFacts ms⌝ ∗
    SupervisorBits.offToken capacity.supervisorBits (SupervisorBits.namesOfEra era cpu))

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def translation (era : Era.Record) (cpu : CPU) : Regime → IProp GF
  | .bare => bare capacity era cpu
  | .kpt N root => KptResidue.residue capacity.translation era cpu N root

/-- Fifty distinct physical keys outside translation: 18 controls, one
mstatus and 31 GPRs. The software x0 fact and all native bit fragments remain.
KPT refresh changes only the separately folded residue, not an unowned field
of this symbolic control file. -/
noncomputable def resources (era : Era.Record) (cpu : CPU) (regime : Regime)
    (control : RegisterFile) (values : HartTp.GprFile) (shares : Shares) : IProp GF :=
  iprop(controls capacity era cpu control shares ∗
    SupervisorBits.msOwnAt capacity.supervisorBits era cpu (control .mstatus) ∗
    SupervisorBits.offToken capacity.supervisorBits (SupervisorBits.namesOfEra era cpu) ∗
    HartTp.pinnedFile capacity.machine.era.registers era cpu values ∗ translation capacity era cpu regime)

/-- A concrete resource frame available to future function composition. It
contains no instruction WP or translation-success assumption. At SIE=0 the
source stack reserve is zero, so depth is the available scratch count. -/
noncomputable def kernelFrame (era : Era.Record) (cpu : CPU) (regime : Regime)
    (tier : KernelDatum.Tier) (ξ : TsoContext.CtxId) (sp : BitVec 64) (depth : Nat) : IProp GF :=
  iprop(⌜Admits regime tier⌝ ∗ TsoContextReadWP.running capacity.machine era cpu ξ ∗
    TimerCap.capability capacity.machine.era.registers era cpu ∗
    KernelStack.own capacity.translation era tier ξ sp depth)

end Xv6.Kernel.MycpuRegimeShell
