import Xv6.Kernel.KernelDatumWord4Proofs

namespace Xv6.Kernel.KernelDatumWord4
open Iris

theorem nativePureSpec : PureSpec := ⟨page_window,vpn_offset,physical_offset,physical_aligned⟩

theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KernelDatumWord4
