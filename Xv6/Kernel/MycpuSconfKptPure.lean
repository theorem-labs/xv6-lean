import Xv6.Kernel.MycpuSconfKptSpec

namespace Xv6.Kernel.MycpuSconfKpt
open MachCSL.Machine

theorem result initial original cpu after values (result : MycpuKpt.Result initial original cpu after values) :
    Result cpu original values := by
  constructor
  · intro key member
    apply result.mapOther
    · intro eq; subst key; simp [MycpuOff.savedIndices] at member
    · intro eq; subst key; simp [MycpuOff.savedIndices] at member
  · exact result.value

theorem stack initial original cpu after values (result : MycpuKpt.Result initial original cpu after values) :
    MycpuKptEntry.sp values = MycpuKptEntry.sp original := by
  exact result.sp

theorem pureSpec : PureSpec := ⟨result, stack⟩

end Xv6.Kernel.MycpuSconfKpt
