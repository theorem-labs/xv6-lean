import Xv6.Kernel.MycpuBareSourceSpec
import Xv6.Kernel.MycpuOffPure

namespace Xv6.Kernel.MycpuBareSource
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

theorem ambient pc control satp pmp (facts : SieOffPacket.Ambient pc control) :
    SieOffPacket.Ambient pc (patch control satp pmp) := by
  exact ⟨⟨facts.pc_eq, facts.next_eq, facts.active, facts.supervisor,
    facts.enable, facts.delegated, facts.environment⟩,
    facts.isa, facts.pma, facts.htif, facts.landing, facts.status, facts.disabled⟩

theorem patch_tor control satp pmp (tor : SupervisorPmp.TorRam pmp) :
    SupervisorPmp.TorRam (patch control satp pmp) :=
  ⟨tor.tor, tor.positive, tor.execute, tor.write, tor.read, tor.covers⟩

theorem config control satp pmp (facts : SieOffPacket.Ambient entryPC control)
    (pma : control .pma_regions = pmaBoot)
    (mode : _get_Satp64_Mode (Mk_Satp64 satp) = 0#4) (tor : SupervisorPmp.TorRam pmp) :
    MycpuOff.EntryConfig (patch control satp pmp) := by
  refine ⟨facts.supervisor, facts.active, ?_, facts.isa,
    facts.environment.2.2.2.2, ?_, ?_, patch_tor control satp pmp tor, facts.htif, pma, facts.pc_eq⟩
  · rcases BitVec.eq_zero_or_eq_one (control .elp) with zero | one
    · exact zero
    · have contradiction := facts.landing
      rw [one] at contradiction
      contradiction
  · change control .mie &&& ~~~(control .mideleg) = 0#64
    rw [facts.enable]
    exact facts.delegated
  · change satpMode_of_bits .RV64 (_get_Satp64_Mode (Mk_Satp64 satp)) = some .Bare
    rw [mode]; rfl

theorem result control cpu original after (good : MycpuOff.Result control cpu original after) :
    Result cpu original (MycpuOff.returnedMap original after) := ⟨good.saved, good.value⟩

theorem stack control cpu original after (good : MycpuOff.Result control cpu original after) :
    sp (MycpuOff.returnedMap original after) = sp original :=
  good.saved 2#5 (by decide)

theorem boundary control cpu original after (before : SieOffPacket.Boundary entryPC control)
    (good : MycpuOff.Result control cpu original after) :
    SieOffPacket.Boundary (returnPC cpu original) after := by
  have enable := good.body.stable .mie (by simp [MycpuBare.stableRegisters])
  have delegation := good.body.stable .mideleg (by simp [MycpuBare.stableRegisters])
  have environment := good.body.stable .menvcfg (by simp [MycpuBare.stableRegisters])
  change after .mie = control .mie at enable
  change after .mideleg = control .mideleg at delegation
  change after .menvcfg = control .menvcfg at environment
  refine ⟨good.body.pc, good.body.nextPC, good.body.config.active,
    good.body.config.privilege, enable.trans before.enable, ?_, ?_⟩
  · rw [delegation]; exact before.delegated
  · rw [environment]; exact before.environment

set_option exponentiation.threshold 1024 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem text : ∀ j : Nat, j < 34 → ∃ b,
    KernelTextImage.sourceMap (MycpuDecode.base + (j : Int)) = some b ∧
      KernelTextImage.value b = nthByte MycpuBootResources.spanWord j := by
  have finite : ∀ j : Fin 34, ∃ b,
      KernelTextImage.sourceMap (MycpuDecode.base + (j.val : Int)) = some b ∧
        KernelTextImage.value b = nthByte MycpuBootResources.spanWord j.val := by decide
  exact fun j bound => finite ⟨j, bound⟩

theorem pureSpec : PureSpec := ⟨config, ambient, result, stack, boundary, text⟩

end Xv6.Kernel.MycpuBareSource
