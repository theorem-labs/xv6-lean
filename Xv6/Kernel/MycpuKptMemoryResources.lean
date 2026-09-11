import Xv6.Kernel.MycpuKptMemoryPure
import Xv6.Kernel.MycpuRegimeShellResources
import MachCSL.Logic.RegisterFootprintProofs

namespace Xv6.Kernel.MycpuKptMemory
open Iris Iris.BI MachCSL.Machine MachCSL.Logic
set_option maxRecDepth 10000

theorem remainder_ra (s : Shares) : remainderFootprint s .ra =
    [(.PC, .own 1), (.nextPC, .own 1), (.minstret, .own 1), (.minstret_increment, .own 1), (.mcountinhibit, .discard), (.minstretcfg, .discard), (.mcycle, .own 1), (.mtime, .own 1), (.mip, .own 1), (.misa, s.misa), (.mie, s.enable), (.mideleg, s.delegation), (.elp, s.landing), (.hart_state, s.hart), (.x3, .own 1), (.x4, .own 1), (.x5, .own 1), (.x6, .own 1), (.x7, .own 1), (.x8, .own 1), (.x9, .own 1), (.x10, .own 1), (.x11, .own 1), (.x12, .own 1), (.x13, .own 1), (.x14, .own 1), (.x15, .own 1), (.x16, .own 1), (.x17, .own 1), (.x18, .own 1), (.x19, .own 1), (.x20, .own 1), (.x21, .own 1), (.x22, .own 1), (.x23, .own 1), (.x24, .own 1), (.x25, .own 1), (.x26, .own 1), (.x27, .own 1), (.x28, .own 1), (.x29, .own 1), (.x30, .own 1), (.x31, .own 1)] := rfl

theorem remainder_s0 (s : Shares) : remainderFootprint s .s0 =
    [(.PC, .own 1), (.nextPC, .own 1), (.minstret, .own 1), (.minstret_increment, .own 1), (.mcountinhibit, .discard), (.minstretcfg, .discard), (.mcycle, .own 1), (.mtime, .own 1), (.mip, .own 1), (.misa, s.misa), (.mie, s.enable), (.mideleg, s.delegation), (.elp, s.landing), (.hart_state, s.hart), (.x1, .own 1), (.x3, .own 1), (.x4, .own 1), (.x5, .own 1), (.x6, .own 1), (.x7, .own 1), (.x9, .own 1), (.x10, .own 1), (.x11, .own 1), (.x12, .own 1), (.x13, .own 1), (.x14, .own 1), (.x15, .own 1), (.x16, .own 1), (.x17, .own 1), (.x18, .own 1), (.x19, .own 1), (.x20, .own 1), (.x21, .own 1), (.x22, .own 1), (.x23, .own 1), (.x24, .own 1), (.x25, .own 1), (.x26, .own 1), (.x27, .own 1), (.x28, .own 1), (.x29, .own 1), (.x30, .own 1), (.x31, .own 1)] := rfl

variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem cells_partition (era : Era.Record) (cpu : CPU) (rs : RegisterFile) s slot :
    iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (MycpuRegimeShell.footprint s) ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (footprint s slot) ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (remainderFootprint s slot)) := by
  cases slot <;>
    simp only [remainder_ra, remainder_s0, MycpuRegimeShell.footprint, MycpuRegimeShell.controlFootprint,
      SupervisorRetirement.pcFootprint, SupervisorRetirement.retirementFootprint,
      SupervisorClock.clockFootprint, show MycpuRegimeShell.gprFootprint = MycpuOff.gprFootprint from rfl,
      MycpuOff.gpr_list, footprint, memoryShares, KptAddress.auxiliaryFootprint,
      MycpuMemory.dataRegister, List.cons_append, List.nil_append, RegisterFootprint.cells]
  · constructor
    · iintro ⟨HPC, HnextPC, Hminstret, Hminstret_increment, Hmcountinhibit, Hminstretcfg, Hmcycle, Hmtime, Hmip, Hcur_privilege, Hmisa, Hmie, Hmideleg, Hmenvcfg, Help, Hpma_regions, Hhtif_tohost_base, Hhart_state, Hmstatus, Hx1, Hx2, Hx3, Hx4, Hx5, Hx6, Hx7, Hx8, Hx9, Hx10, Hx11, Hx12, Hx13, Hx14, Hx15, Hx16, Hx17, Hx18, Hx19, Hx20, Hx21, Hx22, Hx23, Hx24, Hx25, Hx26, Hx27, Hx28, Hx29, Hx30, Hx31, _⟩
      iframe
    · iintro ⟨⟨Hmstatus, Hcur_privilege, Hpma_regions, Hhtif_tohost_base, Hmenvcfg, Hx2, Hx1, _⟩, ⟨HPC, HnextPC, Hminstret, Hminstret_increment, Hmcountinhibit, Hminstretcfg, Hmcycle, Hmtime, Hmip, Hmisa, Hmie, Hmideleg, Help, Hhart_state, Hx3, Hx4, Hx5, Hx6, Hx7, Hx8, Hx9, Hx10, Hx11, Hx12, Hx13, Hx14, Hx15, Hx16, Hx17, Hx18, Hx19, Hx20, Hx21, Hx22, Hx23, Hx24, Hx25, Hx26, Hx27, Hx28, Hx29, Hx30, Hx31, _⟩⟩
      iframe
  · constructor
    · iintro ⟨HPC, HnextPC, Hminstret, Hminstret_increment, Hmcountinhibit, Hminstretcfg, Hmcycle, Hmtime, Hmip, Hcur_privilege, Hmisa, Hmie, Hmideleg, Hmenvcfg, Help, Hpma_regions, Hhtif_tohost_base, Hhart_state, Hmstatus, Hx1, Hx2, Hx3, Hx4, Hx5, Hx6, Hx7, Hx8, Hx9, Hx10, Hx11, Hx12, Hx13, Hx14, Hx15, Hx16, Hx17, Hx18, Hx19, Hx20, Hx21, Hx22, Hx23, Hx24, Hx25, Hx26, Hx27, Hx28, Hx29, Hx30, Hx31, _⟩
      iframe
    · iintro ⟨⟨Hmstatus, Hcur_privilege, Hpma_regions, Hhtif_tohost_base, Hmenvcfg, Hx2, Hx8, _⟩, ⟨HPC, HnextPC, Hminstret, Hminstret_increment, Hmcountinhibit, Hminstretcfg, Hmcycle, Hmtime, Hmip, Hmisa, Hmie, Hmideleg, Help, Hhart_state, Hx1, Hx3, Hx4, Hx5, Hx6, Hx7, Hx9, Hx10, Hx11, Hx12, Hx13, Hx14, Hx15, Hx16, Hx17, Hx18, Hx19, Hx20, Hx21, Hx22, Hx23, Hx24, Hx25, Hx26, Hx27, Hx28, Hx29, Hx30, Hx31, _⟩⟩
      iframe

theorem packet_partition era cpu control values shares slot N root :
    iprop(packet capacity era cpu (.kpt N root) control values shares ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry control cpu values) (footprint shares slot) ∗
      packetFrame capacity era cpu control values shares slot ∗
      KptResidue.residue capacity.translation era cpu N root) := by
  unfold packet
  rw [(MycpuRegimeShell.partition capacity era cpu (.kpt N root) control values shares).to_eq,
    (cells_partition capacity era cpu (entry control cpu values) shares slot).to_eq]
  unfold packetFrame MycpuRegimeShell.translation
  constructor
  · iintro ⟨⟨Hregs,Hrest⟩,Hbits,Hz,Htr⟩; iframe
  · iintro ⟨Hregs,⟨Hrest,Hbits,Hz⟩,Htr⟩; iframe

theorem packet_frame_load era cpu control values shares slot word :
    packetFrame capacity era cpu control (afterMap .load slot values word) shares slot =
    packetFrame capacity era cpu control values shares slot := by
  unfold packetFrame
  rw [entry_load, after_zero]
  cases slot <;> unfold MycpuMemory.after
  all_goals rw [RegisterFootprint.cells_write_other]
  all_goals simp [remainder_ra, remainder_s0]

theorem cells_memory era cpu rs shares slot :
    iprop(RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs (footprint shares slot) ⊣⊢
      KptMemory.auxiliaryCells capacity.translation era cpu rs (memoryShares shares) ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu) rs
        [(.x2,.own 1),(MycpuMemory.dataRegister slot,.own 1)]) :=
  RegisterFootprint.cells_append capacity.machine.era.registers (era.registers cpu) rs _ _

theorem pair_split era cpu tier ξ values words slot :
    iprop(pair capacity era cpu tier ξ values words ⊣⊢
      KernelDatum.word capacity.translation era tier ξ (address cpu values slot) (.own 1) (words slot) ∗
      KernelDatum.word capacity.translation era tier ξ (address cpu values (otherSlot slot)) (.own 1) (words (otherSlot slot))) := by
  cases slot
  · exact .rfl
  · exact sep_comm

theorem pair_close era cpu tier ξ values words kind slot :
    iprop(⊢ KernelDatum.word capacity.translation era tier ξ (address cpu values slot) (.own 1)
        (KptMemory.valueAfter kind (words slot) (sourceValue cpu values slot)) -∗
      KernelDatum.word capacity.translation era tier ξ (address cpu values (otherSlot slot)) (.own 1) (words (otherSlot slot)) -∗
      pair capacity era cpu tier ξ values (afterPair kind slot cpu values words)) := by
  cases kind <;> cases slot <;> simp [pair, afterPair, otherSlot, KptMemory.valueAfter]
  all_goals iintro Hselected Hother; iframe

end Xv6.Kernel.MycpuKptMemory
