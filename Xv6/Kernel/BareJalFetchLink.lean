import Xv6.Kernel.BareJalFetchFoldProofs

namespace Xv6.Kernel.BareJalFetch
open Iris MachCSL.Machine MachCSL.Logic

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity := actual capacity

end Xv6.Kernel.BareJalFetch
