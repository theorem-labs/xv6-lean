import Xv6.Kernel.MycpuFetchProofs

namespace Xv6.Kernel.MycpuFetch
open Iris MachCSL.Machine MachCSL.Logic

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Spec capacity :=
  ⟨wp_fetch capacity, wp_fetch_shared capacity⟩

end Xv6.Kernel.MycpuFetch
