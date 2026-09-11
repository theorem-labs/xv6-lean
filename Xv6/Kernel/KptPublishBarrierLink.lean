import Xv6.Kernel.KptPublishBarrierProofs

namespace Xv6.Kernel.KptPublishBarrier
open Iris MachCSL.Logic

theorem nativeProtocolSpec {GF : BundledGFunctors} (capacity : Capacity GF) : ProtocolSpec capacity where
  boot := protocol_boot capacity
  view := protocol_view capacity

theorem nativeResourceSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : ResourceSpec capacity where
  install := install capacity

theorem nativeSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Spec capacity where
  boot := wp_boot capacity
  view := wp_view capacity

theorem registrySpec [Platform] {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    Spec KptOwnership.registryCapacity := nativeSpec _

end Xv6.Kernel.KptPublishBarrier
