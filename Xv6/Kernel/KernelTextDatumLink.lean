import Xv6.Kernel.KernelTextDatumReadProofs

namespace Xv6.Kernel.KernelTextDatum
open Iris MachCSL.Logic

theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity := actual capacity

theorem nativeWindowSpec {GF : BundledGFunctors} (capacity : Capacity GF) : WindowSpec capacity :=
  actualWindow capacity

theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec KptOwnership.registryCapacity

theorem registryWindowSpec : WindowSpec KptOwnership.registryCapacity :=
  nativeWindowSpec KptOwnership.registryCapacity

end Xv6.Kernel.KernelTextDatum
