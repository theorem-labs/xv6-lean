import MachCSL.Logic.FsDurXferStateProofs

namespace MachCSL.Logic.FsDurXfer

/-- The existing Disk12 camera; allocation chooses only a fresh ghost name. -/
theorem registryMintSpec : MintSpec FsTop.eraCapacity.disk := mintSpec _

theorem registryByteSpec : ByteSpec FsTop.eraCapacity.disk := byteSpec _

/-- Existing Disk12, FsLink23 and FsTop25 capacities, in the same world. -/
theorem registryStateSpec : StateSpec FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity :=
  stateSpec _ _ _

end MachCSL.Logic.FsDurXfer
