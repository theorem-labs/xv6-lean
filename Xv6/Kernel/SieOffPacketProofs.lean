import Xv6.Kernel.SieOffPacketResources

namespace Xv6.Kernel.SieOffPacket
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem open_packet fixed gen era cpu tier ξ file available pc :
    iprop(input capacity fixed gen era cpu tier ξ file available pc ⊢ ∃ regime control,
      ⌜Ambient pc control⌝ ∗ ⌜MycpuRegimeShell.Admits regime.shell tier⌝ ∗
      opened capacity fixed gen era cpu tier ξ file available regime control) := by
  unfold input SieOffCapability.gpr Sconf.sconf Sconf.parts Sconf.interrupts Sconf.environment
  simp only [SieOffCapability.cap, SieOffCapability.rest, SieOffCapability.trapReserve, Nat.zero_add]
  iintro ⟨⟨Hactive, ⟨%ms, Hhw, _, Hpriv, Hms, ⟨%md, Hmie, Hmd, %delegated⟩,
    ⟨%env, Henv, %environment⟩⟩, ⟨Hstack, Hslot, Hoff, Hrun, Htimer, Hwit⟩, Hfile⟩, Hpc⟩
  ihave ⟨%pcRF, %pcs, Hpcs, Hresv⟩ := (SupervisorRetirement.pcIs_iff capacity.machine era cpu pc).mp $$ Hpc
  ihave ⟨%hw, HhwCells, %facts, Hcert, Hhw⟩ :=
    hardware_access capacity fixed gen era cpu $$ Hhw
  ihave ⟨%regime, %admits, Htr, Htoken, Hwit⟩ := split_slot capacity era cpu tier $$ Hslot Hwit
  ihave %status : ⌜SupervisorBits.MsFacts ms⌝ $$ [Hms]
  ·
    isimp [Sconf.msOwn, SupervisorBits.msOwnAt, SupervisorBits.msOwn] at Hms
    icases Hms with ⟨_, _, _, Hfacts⟩
    iexact Hfacts
  isimp [Sconf.msOwn, SupervisorBits.msOwnAt] at Hms
  ihave %disabled := (SupervisorBits.actual capacity.supervisorBits).off (era.registers cpu)
    (SupervisorBits.namesOfEra era cpu) ms $$ Hms Hoff
  ihave Hcontrols := assemble_controls capacity era cpu pcRF hw ms md env $$
    Hpcs HhwCells Hpriv Hmie Hmd Henv Hactive
  iexists regime, assemble pcRF hw ms md env
  isplitr
  · ipureintro; exact assemble_ambient pcRF hw ms md env pc pcs facts status delegated environment disabled
  isplitr
  · ipureintro; exact admits
  unfold opened frame MycpuRegimeShell.resources
  simp only [assemble]
  iframe
  unfold SupervisorBits.msOwnAt
  iexact Hms

theorem close_packet fixed gen era cpu tier ξ file available pc regime control
    (boundary : Boundary pc control) :
    iprop(opened capacity fixed gen era cpu tier ξ file available regime control ⊢
      input capacity fixed gen era cpu tier ξ file available pc) := by
  unfold opened frame MycpuRegimeShell.resources
  iintro ⟨⟨Hcontrols, Hms, Hoff, Hfile, Htr⟩,
    ⟨Hstack, Hrun, Htimer, Hwit, Hhw, Htoken⟩, Hresv⟩
  ihave Hslot := join_slot capacity era cpu regime $$ Htr Htoken
  isimp [MycpuRegimeShell.controls, MycpuRegimeShell.controlFootprint,
    SupervisorRetirement.pcFootprint, SupervisorRetirement.retirementFootprint,
    SupervisorClock.clockFootprint, MycpuRegimeShell.sourceShares,
    List.cons_append, List.nil_append, RegisterFootprint.cells] at Hcontrols
  icases Hcontrols with ⟨Hpc, Hnext, Hret, Hinc, Hinh, Hcfg, Hcycle, Htime, Hmip,
    Hpriv, _, Hmie, Hmd, Henv, _, _, _, Hactive, _⟩
  ihave Hpcs : RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
      control SupervisorRetirement.pcFootprint $$ [Hpc Hnext Hret Hinc Hinh Hcfg Hcycle Htime Hmip]
  ·
    simp only [SupervisorRetirement.pcFootprint, SupervisorRetirement.retirementFootprint,
      SupervisorClock.clockFootprint, List.cons_append, List.nil_append, RegisterFootprint.cells]
    iframe
  ihave HpcIs := SupervisorRetirement.pcIs_intro capacity.machine era cpu control pc
    boundary.pc_eq boundary.next_eq $$ Hpcs Hresv
  isimp [boundary.supervisor] at Hpriv
  isimp [boundary.enable] at Hmie
  isimp [boundary.active] at Hactive
  ihave Hsconf := (Sconf.nativeSpec capacity).intro fixed gen era cpu (control .mstatus)
    (control .mideleg) (control .menvcfg) boundary.delegated boundary.environment $$
    Hhw Hpriv Hms Hmie Hmd Henv
  unfold input SieOffCapability.gpr SieOffCapability.cap SieOffCapability.rest
  simp only [SieOffCapability.trapReserve, Nat.zero_add]
  iframe

theorem partition fixed gen era cpu tier ξ file available regime control :
    iprop(opened capacity fixed gen era cpu tier ξ file available regime control ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (MycpuRegimeShell.entry control cpu file) (MycpuRegimeShell.footprint MycpuRegimeShell.sourceShares) ∗
      MycpuRegimeShell.bitFrame capacity era cpu (control .mstatus) ∗ ⌜file 0#5 = 0#64⌝ ∗
      MycpuRegimeShell.translation capacity era cpu regime.shell ∗
      frame capacity fixed gen era cpu tier ξ file available regime ∗
      Reservations.resvAny capacity.machine.era.reservations era.reservations cpu) := by
  unfold opened
  rw [(MycpuRegimeShell.partition capacity era cpu regime.shell control file MycpuRegimeShell.sourceShares).to_eq]
  constructor
  · iintro ⟨⟨Hcells, Hbits, Hz, Htr⟩, Hframe, Hresv⟩; iframe
  · iintro ⟨Hcells, Hbits, Hz, Htr, Hframe, Hresv⟩; iframe

theorem certificate fixed gen era cpu tier ξ file available regime control :
    iprop(opened capacity fixed gen era cpu tier ξ file available regime control ⊢
      MachineInterp.generationCertificate capacity.machine fixed gen era ∗
      opened capacity fixed gen era cpu tier ξ file available regime control) := by
  unfold opened frame
  iintro ⟨Hpacket, ⟨Hstack, Hrun, Htimer, Hwit, Hhw, Htoken⟩, Hresv⟩
  ihave ⟨%hw, Hcells, Hfacts, Hcert, Hhw⟩ :=
    hardware_access capacity fixed gen era cpu $$ Hhw
  iframe

theorem boot_pma_from_cell fixed gen era cpu tier ξ file available regime control :
    iprop(⊢ opened capacity fixed gen era cpu tier ξ file available regime control -∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .pma_regions .discard pmaBoot -∗
      ⌜control .pma_regions = pmaBoot⌝ ∗
      opened capacity fixed gen era cpu tier ξ file available regime control) := by
  unfold opened MycpuRegimeShell.resources
  iintro ⟨⟨Hcontrols, Hms, Hoff, Hfile, Htr⟩, Hframe, Hresv⟩ Hboot
  simp only [MycpuRegimeShell.controls, MycpuRegimeShell.controlFootprint,
    SupervisorRetirement.pcFootprint, SupervisorRetirement.retirementFootprint,
    SupervisorClock.clockFootprint, MycpuRegimeShell.sourceShares,
    List.cons_append, List.nil_append, RegisterFootprint.cells]
  icases Hcontrols with ⟨Hpc, Hnext, Hret, Hinc, Hinh, Hcfg, Hcycle, Htime, Hmip,
    Hpriv, Hisa, Hmie, Hmd, Henv, Help, Hpma, Hhtif, Hactive, _⟩
  ihave %eq := Registers.regPointsto_agree capacity.machine.era.registers (era.registers cpu)
    .pma_regions .discard .discard (control .pma_regions) pmaBoot $$ [Hpma Hboot]
  · iframe
  iframe
  ipureintro
  exact eq

end Xv6.Kernel.SieOffPacket
