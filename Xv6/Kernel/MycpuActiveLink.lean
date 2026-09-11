import Xv6.Kernel.MycpuActiveProofs

namespace Xv6.Kernel.MycpuActive
open MachCSL.Machine

/-- All factoring, dispatch and preparation contracts are proved; body execution
is deliberately absent from this partial composition specification. -/
theorem actualSpec [Platform] : Spec := ⟨factor, dispatch_plan, prepare_prefix⟩

end Xv6.Kernel.MycpuActive
