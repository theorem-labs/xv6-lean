import Xv6.Kernel.KptPublishProofs

namespace Xv6.Kernel.KptPublish
open Iris MachCSL.Logic

/-- Native physical publication, using the same ownership, context, pin and
view capacities throughout. No physical-tree oracle or fresh era is used. -/
theorem nativeSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Spec capacity where
  pin_word := pin_word capacity
  slot_view := slot_view capacity
  slots_view := slots_view capacity
  page_view := page_view capacity
  tree_view := tree_view capacity
  publish_view := publish_view capacity
  slot_boot := slot_boot capacity
  slots_boot := slots_boot capacity
  page_boot := page_boot capacity
  tree_boot := tree_boot capacity
  publish_boot := publish_boot capacity

theorem nativeAllocationSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : AllocationSpec capacity where
  allocate_view := allocate_view capacity
  allocate_boot := allocate_boot capacity

theorem registrySpec : Spec KptOwnership.registryCapacity := nativeSpec _

theorem registryAllocationSpec {hlc : HasLC} [InvGS_gen hlc KptGhost.registry] :
    AllocationSpec KptOwnership.registryCapacity := nativeAllocationSpec _

end Xv6.Kernel.KptPublish
