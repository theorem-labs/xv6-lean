import Xv6.Kernel.SieOffCapabilityDefs
import MachCSL.Machine.PmaClassDefs

/-! Resource-only source capability adapter to the existing native cycle
shell. General source PMA facts are retained; no instruction WP is assumed. -/
namespace Xv6.Kernel.SieOffPacket
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

abbrev Capacity := MycpuRegimeShell.Capacity
abbrev Tier := KernelDatum.Tier
abbrev File := HartTp.GprFile

/-- The source's root-free slot has exactly these two cases at source kptN. -/
inductive Regime where
  | bare
  | kpt (root : PtTree.PPN)

def Regime.shell : Regime → MycpuRegimeShell.Regime
  | .bare => .bare
  | .kpt root => .kpt KptGhost.kptN root

/-- Only owned projections required to reassemble the exact source boundary.
Nothing constrains arbitrary unowned registers or freezes clock values. -/
structure Boundary (pc : BitVec 64) (control : RegisterFile) : Prop where
  pc_eq : control .PC = pc
  next_eq : control .nextPC = pc
  active : control .hart_state = .HART_ACTIVE ()
  supervisor : control .cur_privilege = .Supervisor
  enable : control .mie = Sconf.mieS
  delegated : Sconf.Delegated (control .mideleg)
  environment : Sconf.EnvironmentFacts (control .menvcfg)

/-- Native source facts extracted on opening. PMA remains the full general
class predicate, never replaced by equality to the boot table. -/
structure Ambient (pc : BitVec 64) (control : RegisterFile) : Prop extends Boundary pc control where
  isa : control .misa = HardwareConfig.misaC
  pma : PmaClass.allowsAll (control .pma_regions)
  htif : control .htif_tohost_base = none
  landing : (control .elp == landing_pad_bits_backwards .LP_EXPECTED) = false
  status : SupervisorBits.MsFacts (control .mstatus)
  disabled : (_get_Mstatus_SIE (control .mstatus) == 1#1) = false

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- The exact linear slot resources outside its physical translation lane.
Bare retains stvec and pending; KPT retains shot. No token is duplicated. -/
def slotToken (era : Era.Record) (cpu : CPU) : Regime → IProp GF
  | .bare => iprop(SupervisorTranslation.pending capacity.translation era cpu ∗
      SupervisorTranslation.stvec capacity.translation era cpu)
  | .kpt _ => SupervisorTranslation.shot capacity.translation era cpu

variable {hlc : HasLC} [InvGS_gen hlc GF]

noncomputable def input (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (file : File) (available : Nat)
    (pc : BitVec 64) : IProp GF :=
  iprop(SieOffCapability.gpr capacity fixed gen era cpu tier ξ file available ∗
    SupervisorRetirement.pcIs capacity.machine era cpu pc)

/-- Explicit source remainder. Whole persistent hardware is retained,
including security/senvcfg/counters/static claims/certificate. The actual
running context and stack stay available for later native memory events. -/
noncomputable def frame (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (file : File) (available : Nat)
    (regime : Regime) : IProp GF :=
  iprop(KernelStack.own capacity.translation era tier ξ (SieOffCapability.sp file) available ∗
    SieOffCapability.running capacity era cpu ξ ∗ SieOffCapability.timer capacity era cpu ∗
    SieOffCapability.tierWitness capacity era cpu tier ∗
    Sconf.hardware capacity fixed gen era cpu ∗ slotToken capacity era cpu regime)

noncomputable def opened (fixed : MachineInterp.FixedNames) (gen : Nat) (era : Era.Record)
    (cpu : CPU) (tier : Tier) (ξ : TsoContext.CtxId) (file : File) (available : Nat)
    (regime : Regime) (control : RegisterFile) : IProp GF :=
  iprop(MycpuRegimeShell.resources capacity era cpu regime.shell control file MycpuRegimeShell.sourceShares ∗
    frame capacity fixed gen era cpu tier ξ file available regime ∗
    Reservations.resvAny capacity.machine.era.reservations era.reservations cpu)

end Xv6.Kernel.SieOffPacket
