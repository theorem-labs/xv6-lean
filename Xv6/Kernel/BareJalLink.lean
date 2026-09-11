import Xv6.Kernel.BareJalProofs
namespace Xv6.Kernel.BareJal
open Iris MachCSL.Logic
variable {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
theorem nativeSpec (capacity : Capacity GF) : Spec capacity := actual capacity
end Xv6.Kernel.BareJal
