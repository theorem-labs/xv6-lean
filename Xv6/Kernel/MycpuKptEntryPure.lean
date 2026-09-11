import Xv6.Kernel.MycpuKptEntrySpec

namespace Xv6.Kernel.MycpuKptEntry
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

theorem config pc control (ambient : SieOffPacket.Ambient pc control)
    (pma : control .pma_regions = pmaBoot) : MycpuKptCycle.Config control := by
  refine ⟨ambient.supervisor, ambient.active, ?_, ambient.isa,
    ambient.environment.2.2.2.2, ?_, pma, ambient.htif⟩
  · rcases BitVec.eq_zero_or_eq_one (control .elp) with zero | one
    · exact zero
    · have contradiction := ambient.landing
      rw [one] at contradiction
      contradiction
  · rw [ambient.enable]
    exact ambient.delegated

theorem slot_ra entrySP : MycpuKptBody.slotAddress entrySP .ra = KernelStack.paStk entrySP 1 := by
  change entrySP - 16#64 + 8#64 = entrySP - 8#64
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

theorem slot_s0 entrySP : MycpuKptBody.slotAddress entrySP .s0 = KernelStack.paStk entrySP 2 := by
  change entrySP - 16#64 + 0#64 = entrySP - 16#64
  exact BitVec.add_zero _

theorem full_regime (regime : SieOffPacket.Regime)
    (admits : MycpuRegimeShell.Admits regime.shell .full) : ∃ root, regime = .kpt root := by
  cases regime with
  | bare => exact False.elim admits
  | kpt root => exact ⟨root, rfl⟩

theorem pureSpec : PureSpec where
  config := config
  slot_ra := slot_ra
  slot_s0 := slot_s0
  full_regime := full_regime

end Xv6.Kernel.MycpuKptEntry
