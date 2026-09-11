import MachCSL.Logic.FsDurEraInstallProofs

namespace MachCSL.Logic.FsDurEraInstall

/-- Logged and snapshot byte families use separate names at the existing
Disk12 camera; these wrappers allocate neither a name nor a world. -/
theorem registrySpec : Spec FsTop.eraCapacity.disk FsTop.linkCapacity := actual _ _

end MachCSL.Logic.FsDurEraInstall
