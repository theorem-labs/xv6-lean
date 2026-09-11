import Xv6.Kernel.MycpuSconfSpec

namespace Xv6.Kernel.MycpuSconf
open MachCSL.Machine

theorem bare_tier (tier : Tier) (admitted : MycpuRegimeShell.Admits .bare tier) : tier = .identity := by
  cases tier with
  | identity => rfl
  | full => exact False.elim admitted

theorem bare_result cpu original after (good : MycpuBareSource.Result cpu original after) :
    Result cpu original after := good

theorem kpt_result cpu original after (good : MycpuKptSource.Result cpu original after) :
    Result cpu original after := good

theorem pureSpec : PureSpec := ⟨bare_tier,bare_result,kpt_result⟩

end Xv6.Kernel.MycpuSconf
