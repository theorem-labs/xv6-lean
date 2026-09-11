import Xv6.Kernel.PushOffCodeProofs

namespace Xv6.Kernel.PushOffCode
open Iris MachCSL.Logic

/-- Complete source byte-resource family; actual instruction decoding and
execution remain separate from this native resource producer. -/
theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity := ⟨code capacity⟩
theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec _

end Xv6.Kernel.PushOffCode
