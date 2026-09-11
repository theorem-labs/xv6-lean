import Xv6.Kernel.PushOffMycpuCallsProofs

namespace Xv6.Kernel.PushOffMycpuCalls
open Iris

theorem nativePureSpec : PureSpec := pureSpec

theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec : Spec MycpuRegimeShell.registryCapacity := nativeSpec _

end Xv6.Kernel.PushOffMycpuCalls
