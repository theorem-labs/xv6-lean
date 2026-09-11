import Xv6.Kernel.BareJalSourceProofs
namespace Xv6.Kernel.BareJalSource
open Iris MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
theorem nativeSpec (capacity : Capacity GF) : Spec capacity := actual capacity
end Xv6.Kernel.BareJalSource
