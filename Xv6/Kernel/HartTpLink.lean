import Xv6.Kernel.HartTpProofs
import MachCSL.Logic.RegisterProofs

namespace Xv6.Kernel.HartTp
open Iris MachCSL.Logic

theorem nativePureSpec : PureSpec := pureSpec

theorem nativeSpec {GF : BundledGFunctors} (capacity : Registers.Capacity GF) : Spec capacity :=
  actual capacity (Registers.registerSpec capacity)

end Xv6.Kernel.HartTp
