import Xv6.Kernel.PushOffWord4Pure
import Xv6.Kernel.MycpuRegimeShellResources
import Xv6.Kernel.KernelDatumWord4Link
import Xv6.Kernel.KptMemory4DataProofs
namespace Xv6.Kernel.PushOffWord4
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem remainder (s : Shares) : remainderFootprint s = [(.PC, .own 1), (.nextPC, .own 1), (.minstret, .own 1), (.minstret_increment, .own 1), (.mcountinhibit, .discard), (.minstretcfg, .discard), (.mcycle, .own 1), (.mtime, .own 1), (.mip, .own 1), (.misa, s.misa), (.mie, s.enable), (.mideleg, s.delegation), (.elp, s.landing), (.hart_state, s.hart), (.x1, .own 1), (.x2, .own 1), (.x3, .own 1), (.x4, .own 1), (.x5, .own 1), (.x6, .own 1), (.x7, .own 1), (.x8, .own 1), (.x9, .own 1), (.x11, .own 1), (.x12, .own 1), (.x13, .own 1), (.x14, .own 1), (.x16, .own 1), (.x17, .own 1), (.x18, .own 1), (.x19, .own 1), (.x20, .own 1), (.x21, .own 1), (.x22, .own 1), (.x23, .own 1), (.x24, .own 1), (.x25, .own 1), (.x26, .own 1), (.x27, .own 1), (.x28, .own 1), (.x29, .own 1), (.x30, .own 1), (.x31, .own 1)] := rfl

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem cells_partition (era : Era.Record) cpu (rs : RegisterFile) s :
    iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (MycpuRegimeShell.footprint s) ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (footprint s) ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (remainderFootprint s)) := by
  simp only [remainder, MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint,
    SupervisorRetirement.pcFootprint, SupervisorRetirement.retirementFootprint, SupervisorClock.clockFootprint,
    show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl, MycpuOff.gpr_list,
    footprint, memoryShares, KptAddress.auxiliaryFootprint, List.cons_append, List.nil_append, RegisterFootprint.cells]
  constructor
  · iintro ⟨HPC,HnextPC,Hminstret,Hminstret_increment,Hmcountinhibit,Hminstretcfg,Hmcycle,Hmtime,Hmip,Hcur_privilege,Hmisa,Hmie,Hmideleg,Hmenvcfg,Help,Hpma_regions,Hhtif_tohost_base,Hhart_state,Hmstatus,Hx1,Hx2,Hx3,Hx4,Hx5,Hx6,Hx7,Hx8,Hx9,Hx10,Hx11,Hx12,Hx13,Hx14,Hx15,Hx16,Hx17,Hx18,Hx19,Hx20,Hx21,Hx22,Hx23,Hx24,Hx25,Hx26,Hx27,Hx28,Hx29,Hx30,Hx31,_⟩; iframe
  · iintro ⟨⟨Hmstatus,Hcur_privilege,Hpma_regions,Hhtif_tohost_base,Hmenvcfg,Hx10,Hx15,_⟩,⟨HPC,HnextPC,Hminstret,Hminstret_increment,Hmcountinhibit,Hminstretcfg,Hmcycle,Hmtime,Hmip,Hmisa,Hmie,Hmideleg,Help,Hhart_state,Hx1,Hx2,Hx3,Hx4,Hx5,Hx6,Hx7,Hx8,Hx9,Hx11,Hx12,Hx13,Hx14,Hx16,Hx17,Hx18,Hx19,Hx20,Hx21,Hx22,Hx23,Hx24,Hx25,Hx26,Hx27,Hx28,Hx29,Hx30,Hx31,_⟩⟩; iframe

theorem packet_common era cpu regime control values shares :
    iprop(packet capacity era cpu regime control values shares ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry control cpu values) (footprint shares) ∗
      packetFrame capacity era cpu control values shares ∗
      MycpuRegimeShell.translation capacity era cpu regime) := by
  unfold packet
  rw [(MycpuRegimeShell.partition capacity era cpu regime control values shares).to_eq,
    (cells_partition capacity era cpu (entry control cpu values) shares).to_eq]
  unfold packetFrame
  constructor
  · iintro ⟨⟨Hregs,Hrest⟩,Hbits,Hz,Htr⟩; iframe
  · iintro ⟨Hregs,⟨Hrest,Hbits,Hz⟩,Htr⟩; iframe

theorem packet_kpt era cpu control values shares N root :
    iprop(packet capacity era cpu (.kpt N root) control values shares ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry control cpu values) (footprint shares) ∗
      KptResidue.residue capacity.translation era cpu N root ∗ packetFrame capacity era cpu control values shares) := by
  unfold packet
  rw [(MycpuRegimeShell.partition capacity era cpu (.kpt N root) control values shares).to_eq,
    (cells_partition capacity era cpu (entry control cpu values) shares).to_eq]
  unfold packetFrame MycpuRegimeShell.translation
  constructor
  · iintro ⟨⟨Hregs,Hrest⟩,Hbits,Hz,Htr⟩; iframe
  · iintro ⟨Hregs,Htr,⟨Hrest,Hbits,Hz⟩⟩; iframe

theorem packet_frame_load era cpu control values shares (old : BitVec 32) :
    packetFrame capacity era cpu control (HartTp.set values 15#5 (old.signExtend 64)) shares =
    packetFrame capacity era cpu control values shares := by
  unfold packetFrame
  rw [entry_load]
  have z : HartTp.set values 15#5 (old.signExtend 64) 0#5 = values 0#5 := HartTp.set_other _ _ _ _ (by decide)
  rw [z, RegisterFootprint.cells_write_other]
  simp [remainder]

theorem packet_bare era cpu control values s :
    iprop(packet capacity era cpu .bare control values s ⊣⊢ barePacket capacity era cpu control values s) := by
  unfold packet
  rw [(MycpuRegimeShell.partition capacity era cpu .bare control values s).to_eq]
  simp only [MycpuRegimeShell.translation, MycpuRegimeShell.bare, barePacket, fullBareFootprint,
    MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint,
    SupervisorRetirement.pcFootprint,SupervisorRetirement.retirementFootprint,SupervisorClock.clockFootprint,
    show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl,MycpuOff.gpr_list,
    SupervisorPmp.config,SupervisorPmp.footprint,List.cons_append,List.nil_append,RegisterFootprint.cells,
    entry,MycpuRegimeShell.entry,MycpuOff.entry,MycpuBareSource.patch]
  constructor
  · iintro ⟨⟨HPC,HnextPC,Hminstret,Hminstret_increment,Hmcountinhibit,Hminstretcfg,Hmcycle,Hmtime,Hmip,Hcur_privilege,Hmisa,Hmie,Hmideleg,Hmenvcfg,Help,Hpma_regions,Hhtif_tohost_base,Hhart_state,Hmstatus,Hx1,Hx2,Hx3,Hx4,Hx5,Hx6,Hx7,Hx8,Hx9,Hx10,Hx11,Hx12,Hx13,Hx14,Hx15,Hx16,Hx17,Hx18,Hx19,Hx20,Hx21,Hx22,Hx23,Hx24,Hx25,Hx26,Hx27,Hx28,Hx29,Hx30,Hx31,_⟩,Hbits,Hz,%satp,Hsatp,%mode,%pmp,%tor,Hpmp⟩
    icases Hpmp with ⟨Hpmpcfg_n,Hpmpaddr_n,_⟩
    iexists satp,pmp
    iframe
    ipureintro; exact ⟨mode,tor⟩
  · iintro ⟨%satp,%pmp,%facts,⟨HPC,HnextPC,Hminstret,Hminstret_increment,Hmcountinhibit,Hminstretcfg,Hmcycle,Hmtime,Hmip,Hcur_privilege,Hmisa,Hmie,Hmideleg,Hmenvcfg,Help,Hpma_regions,Hhtif_tohost_base,Hhart_state,Hmstatus,Hx1,Hx2,Hx3,Hx4,Hx5,Hx6,Hx7,Hx8,Hx9,Hx10,Hx11,Hx12,Hx13,Hx14,Hx15,Hx16,Hx17,Hx18,Hx19,Hx20,Hx21,Hx22,Hx23,Hx24,Hx25,Hx26,Hx27,Hx28,Hx29,Hx30,Hx31,Hsatp,Hpmpcfg_n,Hpmpaddr_n,_⟩,Hbits,Hz⟩
    iframe HPC HnextPC Hminstret Hminstret_increment Hmcountinhibit Hminstretcfg Hmcycle Hmtime Hmip Hcur_privilege Hmisa Hmie Hmideleg Hmenvcfg Help Hpma_regions Hhtif_tohost_base Hhart_state Hmstatus Hx1 Hx2 Hx3 Hx4 Hx5 Hx6 Hx7 Hx8 Hx9 Hx10 Hx11 Hx12 Hx13 Hx14 Hx15 Hx16 Hx17 Hx18 Hx19 Hx20 Hx21 Hx22 Hx23 Hx24 Hx25 Hx26 Hx27 Hx28 Hx29 Hx30 Hx31 Hbits Hz
    iexists satp
    iframe Hsatp
    isplitr
    · ipureintro; exact facts.1
    iexists pmp
    iframe
    ipureintro; exact facts.2

theorem identity_word era ξ va dq old :
    iprop(KernelDatumWord4.word capacity.translation era .identity ξ va dq old ⊢
      ⌜KernelDatumWord4.Aligned va ∧ SupervisorPhysical.RamRange va 4⌝ ∗
      TsoContextBytesReadWP.window capacity.machine era ξ va 4 dq old ∗
      (∀ newValue, TsoContextBytesReadWP.window capacity.machine era ξ va 4 dq newValue -∗
        KernelDatumWord4.word capacity.translation era .identity ξ va dq newValue)) := by
  iintro Hword
  ihave %aligned := KptMemory4.word_aligned capacity.translation era .identity ξ va dq old $$ Hword
  ihave ⟨%ppn,Hclaims,Hphysical,Hclose⟩ := (KernelDatumWord4.nativeSpec capacity.translation).access era .identity ξ va dq old $$ Hword
  ihave Hclaim := (KernelDatumWord4.nativeSpec capacity.translation).head era .identity va ppn $$ Hclaims
  iunfold KernelDatum.claim at Hclaim
  icases Hclaim with ⟨_,%facts⟩
  have same : KernelDatum.physical ppn va = va := facts.2.2
  have ram : KernelDatum.Ram va := by simpa only [same] using facts.2.1
  isimp only [same] at Hphysical Hclose
  iunfold KernelDatumWord4.physicalWord at Hphysical
  icases Hphysical with ⟨_,Hwindow⟩
  iframe Hwindow
  isplitr
  · ipureintro; exact ⟨aligned,KptMemory4.data_range va aligned ram⟩
  iintro %newValue Hwindow
  iapply Hclose $$ %newValue
  unfold KernelDatumWord4.physicalWord
  iframe
theorem bare_cells_partition (era : Era.Record) cpu (rs : RegisterFile) s :
    iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (fullBareFootprint s) ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (bareFootprint s) ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (remainderFootprint s)) := by
  simp only [remainder,fullBareFootprint,MycpuRegimeShell.footprint,MycpuRegimeShell.controlFootprint,
    SupervisorRetirement.pcFootprint,SupervisorRetirement.retirementFootprint,SupervisorClock.clockFootprint,
    show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl,MycpuOff.gpr_list,
    bareFootprint,bareShares,PushOffWord4Bare.footprint,SupervisorBareFetch.footprint,
    SupervisorBare.footprint,SupervisorFetchRead.footprint,List.cons_append,List.nil_append,RegisterFootprint.cells]
  constructor
  · iintro ⟨HPC,HnextPC,Hminstret,Hminstret_increment,Hmcountinhibit,Hminstretcfg,Hmcycle,Hmtime,Hmip,Hcur_privilege,Hmisa,Hmie,Hmideleg,Hmenvcfg,Help,Hpma_regions,Hhtif_tohost_base,Hhart_state,Hmstatus,Hx1,Hx2,Hx3,Hx4,Hx5,Hx6,Hx7,Hx8,Hx9,Hx10,Hx11,Hx12,Hx13,Hx14,Hx15,Hx16,Hx17,Hx18,Hx19,Hx20,Hx21,Hx22,Hx23,Hx24,Hx25,Hx26,Hx27,Hx28,Hx29,Hx30,Hx31,Hsatp,Hpmpcfg_n,Hpmpaddr_n,_⟩; iframe
  · iintro ⟨⟨Hmenvcfg,Hmstatus,Hcur_privilege,Hsatp,Hpma_regions,Hpmpcfg_n,Hpmpaddr_n,Hhtif_tohost_base,Hx10,Hx15,_⟩,⟨HPC,HnextPC,Hminstret,Hminstret_increment,Hmcountinhibit,Hminstretcfg,Hmcycle,Hmtime,Hmip,Hmisa,Hmie,Hmideleg,Help,Hhart_state,Hx1,Hx2,Hx3,Hx4,Hx5,Hx6,Hx7,Hx8,Hx9,Hx11,Hx12,Hx13,Hx14,Hx16,Hx17,Hx18,Hx19,Hx20,Hx21,Hx22,Hx23,Hx24,Hx25,Hx26,Hx27,Hx28,Hx29,Hx30,Hx31,_⟩⟩; iframe

theorem cells_memory era cpu rs shares :
    iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (footprint shares) ⊣⊢
      KptMemory4.auxiliaryCells capacity.translation era cpu rs (memoryShares shares) ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs [(.x10,.own 1),(.x15,.own 1)]) :=
  RegisterFootprint.cells_append capacity.machine.era.registers (era.registers cpu) rs _ _

theorem cells_bare_memory era cpu rs shares :
    iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (bareFootprint shares) ⊣⊢
      PushOffWord4Bare.cells capacity.machine era cpu rs (bareShares shares) ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs [(.x10,.own 1),(.x15,.own 1)]) :=
  RegisterFootprint.cells_append capacity.machine.era.registers (era.registers cpu) rs _ _

theorem nativeResourceSpec : ResourceSpec capacity :=
  ⟨packet_kpt capacity, packet_bare capacity, identity_word capacity⟩
end Xv6.Kernel.PushOffWord4
