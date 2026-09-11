import MachCSL.Logic.FsDurSnapshotAllocProofs
import MachCSL.Logic.FsTopLink

namespace MachCSL.Logic.FsDurSnapshot
open Iris Iris.Std Iris.BI Xv6.Fs DurableState

/-- The current registry uses the same physical-disk camera for a distinct
snapshot name; link and top resources use their existing slots. -/
noncomputable def registryPdur (disk : BlockMap) : IProp FsTop.registry :=
  Pdur FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity disk

theorem disk_slot : FsTop.eraCapacity.disk.image.elem.τ = 12 := rfl
theorem link_slot : FsTop.linkCapacity.link.τ = 23 := rfl
theorem top_slot : FsTop.registryCapacity.top.elem.τ = 25 := rfl

namespace Initial

/-- Initial-only constructor with the existing physical disk authority retained
unchanged. The frame can include every other machine and caller resource.
The ordinary update theorem does not itself enforce epoch-zero use. -/
theorem preserve_physical_authority (state : State) disk (ok : Snapshot.OK state disk)
    (physicalName : GName) (physicalDisk : Devices.Virtio.Disk) (frame : IProp FsTop.registry) :
    iprop(Disk.imageAuth FsTop.eraCapacity.disk physicalName physicalDisk ∗ frame ⊢ |==>
      (registryPdur disk ∗ Disk.imageAuth FsTop.eraCapacity.disk physicalName physicalDisk ∗ frame)) :=
  P_dur_alloc FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity state disk ok
    (iprop(Disk.imageAuth FsTop.eraCapacity.disk physicalName physicalDisk ∗ frame))

/-- The same preservation fact for an explicitly known finite map authority. -/
theorem preserve_map_authority (state : State) disk (ok : Snapshot.OK state disk)
    (physicalName : GName) (physicalMap : FsDurBytes.ByteMap) (frame : IProp FsTop.registry) :
    iprop(Disk.mapAuth FsTop.eraCapacity.disk physicalName physicalMap ∗ frame ⊢ |==>
      (registryPdur disk ∗ Disk.mapAuth FsTop.eraCapacity.disk physicalName physicalMap ∗ frame)) :=
  P_dur_alloc FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity state disk ok
    (iprop(Disk.mapAuth FsTop.eraCapacity.disk physicalName physicalMap ∗ frame))

end Initial
end MachCSL.Logic.FsDurSnapshot
