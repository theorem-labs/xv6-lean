import MachCSL.Logic.IcacheRegionBootProofs
import MachCSL.Logic.IcacheRegionSlotLink

namespace MachCSL.Logic.IcacheRegionBoot

/-- Existing same-world capacities; only the source record camera gets a fresh name. -/
theorem nativeSpec : Spec IcacheRegionSlot.nativeCapacity := actual _

end MachCSL.Logic.IcacheRegionBoot
