import Xv6.Kernel.KernelTextImageProofs

namespace Xv6.Kernel.KernelTextImage
open Iris MachCSL.Logic

theorem nativePureSpec : PureSpec := actualPure

theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity := actual capacity

theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

end Xv6.Kernel.KernelTextImage
