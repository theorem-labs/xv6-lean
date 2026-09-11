import Xv6.Kernel.MycpuRegimeShellPlan
import Xv6.Kernel.MycpuOffResources
import MachCSL.Logic.SupervisorBitsSpec

namespace Xv6.Kernel.MycpuRegimeShell
open Iris Iris.BI MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF] (capacity : Capacity GF)

theorem partition era cpu regime control values shares :
    iprop(resources capacity era cpu regime control values shares ⊣⊢
      RegisterFootprint.cells capacity.machine.era.registers (era.registers cpu)
        (entry control cpu values) (footprint shares) ∗
      bitFrame capacity era cpu (control .mstatus) ∗ ⌜values 0#5 = 0#64⌝ ∗
      translation capacity era cpu regime) := by
  unfold resources
  rw [show HartTp.pinnedFile capacity.machine.era.registers era cpu values =
    iprop(⌜values 0#5 = 0#64⌝ ∗ RegisterFootprint.cells capacity.machine.era.registers
      (era.registers cpu) (entry control cpu values) gprFootprint) from rfl]
  have gprs : gprFootprint = MycpuOff.gprFootprint := rfl
  simp only [controls, footprint, controlFootprint, SupervisorRetirement.pcFootprint,
    SupervisorRetirement.retirementFootprint, SupervisorClock.clockFootprint,
    SupervisorBits.msOwnAt, SupervisorBits.msOwn, bitFrame, Capacity.supervisorBits,
    gprs, MycpuOff.gpr_list, List.cons_append, List.nil_append,
    RegisterFootprint.cells, entry, MycpuOff.entry]
  constructor
  · iintro ⟨⟨HPC, Hnext, Hret, Hflag, Hinh, Hcfg, Hcy, Htime, Hmip, Hpriv, Hmisa,
      Hmie, Hdeleg, Henv, Help, Hpma, Hhtif, Hhart, _⟩,
      ⟨Hms, Hsie, Hsret, Hfacts⟩, Hoff, ⟨Hz,
      ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16,
       H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29, H30, H31, _⟩⟩, Htr⟩
    iframe
  · iintro ⟨⟨HPC, Hnext, Hret, Hflag, Hinh, Hcfg, Hcy, Htime, Hmip, Hpriv, Hmisa,
      Hmie, Hdeleg, Henv, Help, Hpma, Hhtif, Hhart, Hms,
      H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16,
      H17, H18, H19, H20, H21, H22, H23, H24, H25, H26, H27, H28, H29, H30, H31, _⟩,
      ⟨Hsie, Hsret, Hfacts, Hoff⟩, Hz, Htr⟩
    iframe

theorem disabled (bits : SupervisorBits.Spec capacity.supervisorBits) era cpu regime control values shares :
    iprop(resources capacity era cpu regime control values shares ⊢
      ⌜(_get_Mstatus_SIE (control .mstatus) == 1#1) = false ∧
        entry control cpu values .x4 = HartTp.hartWord cpu⌝) := by
  unfold resources
  iintro ⟨_, Hms, Hoff, _, _⟩
  isimp [SupervisorBits.msOwnAt] at Hms
  ihave %off := bits.off (era.registers cpu) (SupervisorBits.namesOfEra era cpu) (control .mstatus) $$ Hms Hoff
  ipureintro
  exact ⟨off, rfl⟩

end Xv6.Kernel.MycpuRegimeShell
