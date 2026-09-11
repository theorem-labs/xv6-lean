import MachCSL.Logic.DiskProofs
import MachCSL.Logic.DiskRegistry
import MachCSL.Logic.PowerGhostLink

/-! Explicit contracts instantiated in the registry extended at disk-image slot 12. -/
namespace MachCSL.Logic.Disk

theorem registryDiskSpec : DiskSpec registryCapacity := diskSpec registryCapacity

theorem registryPowerGhostSpec : PowerGhost.PowerGhostSpec powerCapacity :=
  PowerGhost.powerGhostSpec powerCapacity

end MachCSL.Logic.Disk
