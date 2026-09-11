import Xv6.Kernel.KptJalSconfSpec
import Xv6.Kernel.MycpuCycleShellProofs

namespace Xv6.Kernel.KptJalSconf
open MachCSL.Machine MachCSL.Logic

theorem stack pc file : SieOffCapability.sp (afterFile pc file) = SieOffCapability.sp file := rfl

theorem saved pc file : MycpuOff.Saved file (afterFile pc file) := by
  intro key member
  have different : key ≠ 1#5 := by
    intro same; subst key; simp [MycpuOff.savedIndices] at member
  exact if_neg different

theorem boundary pc imm initial after (before : SieOffPacket.Boundary pc initial)
    (done : MycpuRegimeShell.Completed (KptJal.afterControl pc imm (KptJal.started initial)) after) :
    SieOffPacket.Boundary (KptJal.target pc imm) after := by
  have pcs := MycpuCycleShell.completed_pc _ _ done
  have same := MycpuCycleShell.completed_other _ _ done
  refine ⟨pcs.1,pcs.2,?_,?_,?_,?_,?_⟩
  · rw [same .hart_state (by decide) (by decide) (by decide)]; exact before.active
  · rw [same .cur_privilege (by decide) (by decide) (by decide)]; exact before.supervisor
  · rw [same .mie (by decide) (by decide) (by decide)]; exact before.enable
  · rw [same .mideleg (by decide) (by decide) (by decide)]; exact before.delegated
  · rw [same .menvcfg (by decide) (by decide) (by decide)]; exact before.environment

theorem pureSpec : PureSpec := ⟨stack,saved,boundary⟩

end Xv6.Kernel.KptJalSconf
