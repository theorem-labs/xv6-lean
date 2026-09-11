import Xv6.Kernel.SieOffPacketSpec
import Xv6.Kernel.SieOffCapabilityLink
import Xv6.Kernel.HardwareConfigLink
import MachCSL.Logic.SupervisorRetirementProofs

namespace Xv6.Kernel.SieOffPacket
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

/-- Assemble only the owned control projections. The remaining entries are
inherited from the pc resource's existential file, not a physical-file claim. -/
def assemble (pc : RegisterFile) (hw : HardwareConfig.Values) (ms delegation environment : BitVec 64) : RegisterFile
  | .cur_privilege => .Supervisor
  | .misa => hw.isa
  | .mie => Sconf.mieS
  | .mideleg => delegation
  | .menvcfg => environment
  | .elp => hw.landing
  | .pma_regions => hw.regions
  | .htif_tohost_base => none
  | .hart_state => .HART_ACTIVE ()
  | .mstatus => ms
  | r => pc r

theorem assemble_ambient pc hw ms delegation environment address
    (pcs : pc .PC = address ∧ pc .nextPC = address)
    (facts : HardwareConfig.Facts hw) (status : SupervisorBits.MsFacts ms)
    (delegated : Sconf.Delegated delegation) (env : Sconf.EnvironmentFacts environment)
    (disabled : (_get_Mstatus_SIE ms == 1#1) = false) :
    Ambient address (assemble pc hw ms delegation environment) := by
  refine ⟨⟨pcs.1, pcs.2, rfl, rfl, rfl, delegated, env⟩,
    ?_, ?_, rfl, ?_, status, disabled⟩
  · exact HardwareConfig.pureSpec.isa hw facts
  · exact HardwareConfig.pureSpec.pma hw facts
  · exact facts.2.2.2.2.2.2.2.1

variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem assemble_controls era cpu pc hw ms delegation environment :
    iprop(⊢ RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) pc
        SupervisorRetirement.pcFootprint -∗
      HardwareConfig.cells capacity.translation era cpu .discard hw -∗
      Sconf.cell capacity era cpu .cur_privilege .Supervisor -∗
      Sconf.cell capacity era cpu .mie Sconf.mieS -∗ Sconf.cell capacity era cpu .mideleg delegation -∗
      Sconf.cell capacity era cpu .menvcfg environment -∗ SieOffCapability.active capacity era cpu -∗
      MycpuRegimeShell.controls capacity era cpu (assemble pc hw ms delegation environment)
        MycpuRegimeShell.sourceShares) := by
  simp only [SupervisorRetirement.pcFootprint, SupervisorRetirement.retirementFootprint,
    SupervisorClock.clockFootprint, List.cons_append, List.nil_append, RegisterFootprint.cells,
    HardwareConfig.cells, Sconf.cell, SieOffCapability.active, MycpuRegimeShell.controls,
    MycpuRegimeShell.controlFootprint, MycpuRegimeShell.sourceShares, assemble]
  iintro ⟨Hpc, Hnext, Hret, Hinc, Hinh, Hcfg, Hcycle, Htime, Hmip, _⟩
    ⟨Hisa, _, Hpma, Hhtif, Help, _, _, _⟩ Hpriv Hmie Hmd Henv Hactive
  iframe

/-- Structural projection is proved before instantiating the large static map. -/
private theorem trim_hardware {α : Type} (C : α → IProp GF) (F : α → Prop)
    (P Q H : IProp GF) :
    iprop((∃ v, C v ∗ ⌜F v⌝ ∗ P ∗ Q ∗ H) ⊢ ∃ v, C v ∗ ⌜F v⌝ ∗ Q ∗ H) := by
  iintro ⟨%v, HC, HF, _, HQ, HH⟩
  iexists v
  iframe

theorem hardware_access fixed gen era cpu :
    iprop(Sconf.hardware capacity fixed gen era cpu ⊢ ∃ v,
      HardwareConfig.cells capacity.translation era cpu .discard v ∗ ⌜HardwareConfig.Facts v⌝ ∗
      MachineInterp.generationCertificate capacity.machine fixed gen era ∗
      Sconf.hardware capacity fixed gen era cpu) :=
  ((HardwareConfig.nativeSpec capacity.translation).access fixed gen era cpu).trans
    (trim_hardware (fun v => HardwareConfig.cells capacity.translation era cpu .discard v)
      HardwareConfig.Facts _ _ _)

variable {hlc : HasLC} [InvGS_gen hlc GF]

theorem split_slot era cpu tier :
    iprop(⊢ SupervisorTranslation.sourceSlot capacity.translation era cpu -∗
      SieOffCapability.tierWitness capacity era cpu tier -∗ ∃ regime,
      ⌜MycpuRegimeShell.Admits regime.shell tier⌝ ∗
      MycpuRegimeShell.translation capacity era cpu regime.shell ∗ slotToken capacity era cpu regime ∗
      SieOffCapability.tierWitness capacity era cpu tier) := by
  unfold SupervisorTranslation.sourceSlot SupervisorTranslation.slot
  iintro Hslot Hwit
  icases Hslot with (⟨Hpending, Hbare, Hstvec⟩ | ⟨Hshot, ⟨%root, Hresidue⟩⟩)
  · cases tier with
    | identity =>
      iexists Regime.bare
      isplitr
      · ipureintro; trivial
      · simp only [Regime.shell, MycpuRegimeShell.translation, MycpuRegimeShell.bare,
          SupervisorTranslation.bare, KptResidue.satpCell, KptResidue.pmpConfig,
          SupervisorTranslation.BareSatp, slotToken]
        iframe
    | full =>
      unfold SieOffCapability.tierWitness
      ihave %impossible := (SupervisorTranslation.nativeSpec capacity.translation).on_pending_false era cpu $$ Hwit Hpending
      exact False.elim impossible
  · iexists Regime.kpt root
    isplitr
    · ipureintro; cases tier <;> trivial
    · simp only [Regime.shell, MycpuRegimeShell.translation, slotToken]
      iframe

theorem join_slot era cpu regime :
    iprop(⊢ MycpuRegimeShell.translation capacity era cpu regime.shell -∗
      slotToken capacity era cpu regime -∗ SupervisorTranslation.sourceSlot capacity.translation era cpu) := by
  cases regime with
  | bare =>
    simp only [Regime.shell, MycpuRegimeShell.translation, MycpuRegimeShell.bare, slotToken]
    iintro Hbare ⟨Hpending, Hstvec⟩
    unfold SupervisorTranslation.sourceSlot SupervisorTranslation.slot
    ileft
    iframe Hpending Hstvec
    unfold SupervisorTranslation.bare SupervisorTranslation.BareSatp KptResidue.satpCell KptResidue.pmpConfig
    iexact Hbare
  | kpt root =>
    simp only [Regime.shell, MycpuRegimeShell.translation, slotToken]
    iintro Hres Hshot
    iapply (SupervisorTranslation.nativeSpec capacity.translation).intro_kpt era cpu KptGhost.kptN root $$ Hshot Hres

end Xv6.Kernel.SieOffPacket
