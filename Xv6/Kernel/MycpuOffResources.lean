import Xv6.Kernel.MycpuOffPure
import MachCSL.Logic.RegisterFootprintProofs

namespace Xv6.Kernel.MycpuOff
open Iris Iris.BI Iris.ProofMode MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem gpr_eq era cpu control values :
    HartTp.pinnedFile capacity.machine.era.registers era cpu values =
    iprop(⌜values 0#5 = 0#64⌝ ∗ RegisterFootprint.cells capacity.machine.era.registers
      (era.registers cpu) (entry control cpu values) gprFootprint) := by rfl

/-- The physical partition is a reversible separation equivalence. -/
theorem partition era cpu control values shares :
    iprop(controls capacity era cpu control shares ∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .mstatus (.own 1) (control .mstatus) ∗
      HartTp.pinnedFile capacity.machine.era.registers era cpu values ⊣⊢
      MycpuBare.cells capacity.machine era cpu (entry control cpu values) (cycleShares shares) ∗
      MycpuBare.calleeFrame capacity.machine era cpu (entry control cpu values) (fun _ => .own 1) ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry control cpu values) framedFootprint ∗ ⌜values 0#5 = 0#64⌝) := by
  rw [gpr_eq capacity era cpu control values]
  simp only [controls, MycpuBare.calleeFrame, MycpuBare.frameFootprint,
    MycpuBare.remainingSaved, MycpuBare.cells, MycpuCycle.cells, MycpuCycleBody.cells,
    control_list, cycle_list, gpr_list, framedFootprint, framedRegisters,
    List.map_cons, List.map_nil, RegisterFootprint.cells, entry]
  constructor
  · iintro ⟨⟨HPC, Hmisa, Hcur_privilege, Hsatp, Hpma_regions, Hpmpcfg_n, Hpmpaddr_n, Hhtif_tohost_base, Hmie, Hmideleg, Hmenvcfg, Help, HnextPC, Hminstret, Hminstret_increment, Hmcountinhibit, Hminstretcfg, Hmcycle, Hmtime, Hmip, Hhart_state, _⟩, Hmstatus, Hz, ⟨Hx1, Hx2, Hx3, Hx4, Hx5, Hx6, Hx7, Hx8, Hx9, Hx10, Hx11, Hx12, Hx13, Hx14, Hx15, Hx16, Hx17, Hx18, Hx19, Hx20, Hx21, Hx22, Hx23, Hx24, Hx25, Hx26, Hx27, Hx28, Hx29, Hx30, Hx31, _⟩⟩
    iframe
  · iintro ⟨⟨HPC, Hmisa, Hmstatus, Hcur_privilege, Hsatp, Hpma_regions, Hpmpcfg_n, Hpmpaddr_n, Hhtif_tohost_base, Hmie, Hmideleg, Hmenvcfg, Help, HnextPC, Hx1, Hx2, Hx8, Hx15, Hx10, Hx4, Hminstret, Hminstret_increment, Hmcountinhibit, Hminstretcfg, Hmcycle, Hmtime, Hmip, Hhart_state, _⟩, ⟨Hx9, Hx18, Hx19, Hx20, Hx21, Hx22, Hx23, Hx24, Hx25, Hx26, Hx27, _⟩, ⟨Hx3, Hx5, Hx6, Hx7, Hx11, Hx12, Hx13, Hx14, Hx16, Hx17, Hx28, Hx29, Hx30, Hx31, _⟩, Hz⟩
    iframe

theorem cells_eq γ (left right : RegisterFile) (fp : RegisterFootprint.Footprint)
    (agree : ∀ r ∈ fp.map Prod.fst, left r = right r) :
    RegisterFootprint.cells capacity.machine.era.registers γ left fp =
      RegisterFootprint.cells capacity.machine.era.registers γ right fp := by
  induction fp with
  | nil => rfl
  | cons cell rest ih =>
    rcases cell with ⟨r, dq⟩
    simp only [RegisterFootprint.cells]
    rw [agree r (by simp), ih (by intro r member; exact agree r (by simp [member]))]

theorem returned_cycle_eq era cpu control values after shares
    (result : MycpuBare.HartResult (entry control cpu values) after cpu) :
    MycpuBare.cells capacity.machine era cpu (entry after cpu (returnedMap values after)) (cycleShares shares) =
      MycpuBare.cells capacity.machine era cpu after (cycleShares shares) := by
  apply cells_eq
  intro r member
  exact returned_agrees control cpu values after result r (cycle_owned shares r member)

theorem returned_saved_eq era cpu control values after
    (result : MycpuBare.HartResult (entry control cpu values) after cpu) :
    MycpuBare.calleeFrame capacity.machine era cpu (entry after cpu (returnedMap values after)) (fun _ => .own 1) =
      MycpuBare.calleeFrame capacity.machine era cpu after (fun _ => .own 1) := by
  apply cells_eq
  intro r member
  have actual : r ∈ MycpuBare.remainingSaved := by
    simpa [MycpuBare.frameFootprint, List.map_map] using member
  exact returned_agrees control cpu values after result r (saved_owned r actual)

theorem framed_eq (era : Era.Record) (cpu : CPU) control values after :
    RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
      (entry after cpu (returnedMap values after)) framedFootprint =
    RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
      (entry control cpu values) framedFootprint := by
  apply cells_eq
  intro r member
  have actual : r ∈ framedRegisters := by simpa [framedFootprint, List.map_map] using member
  exact framed_entry control cpu values after r actual

theorem reassemble era cpu control values after shares
    (result : MycpuBare.HartResult (entry control cpu values) after cpu) :
    iprop(MycpuBare.cells capacity.machine era cpu after (cycleShares shares) ∗
      MycpuBare.calleeFrame capacity.machine era cpu after (fun _ => .own 1) ∗
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry control cpu values) framedFootprint ∗ ⌜values 0#5 = 0#64⌝ ⊢
      controls capacity era cpu after shares ∗
      Registers.regPointsto capacity.machine.era.registers (era.registers cpu) .mstatus (.own 1) (after .mstatus) ∗
      HartTp.pinnedFile capacity.machine.era.registers era cpu (returnedMap values after)) := by
  have rejoin := (partition capacity era cpu after (returnedMap values after) shares).2
  rw [returned_cycle_eq capacity era cpu control values after shares result,
    returned_saved_eq capacity era cpu control values after result,
    framed_eq capacity era cpu control values after] at rejoin
  exact rejoin

end Xv6.Kernel.MycpuOff
