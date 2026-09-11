import Xv6.Kernel.MycpuBareLink

namespace Xv6.Kernel.MycpuBare
open MachCSL.Machine

/-- The bookkeeping result itself satisfies the public result predicate.
A separate actual-machine witness establishes operational inhabitation. -/
theorem reference_result (entry : RegisterFile) (config : EntryConfig entry) :
    Result entry (reference entry 14) :=
  phase_result config ⟨CoreEq.refl _, rfl, fun _ => rfl⟩

end Xv6.Kernel.MycpuBare
