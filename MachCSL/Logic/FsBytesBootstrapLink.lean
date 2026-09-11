import MachCSL.Logic.FsBytesBootstrapProofs
import MachCSL.Logic.FsBlockGhostLink

namespace MachCSL.Logic.FsBytesBootstrap
open Iris

abbrev registry := FsBlockGhost.registry

def nativeCapacity : Capacity registry := ⟨FsBlockGhost.nativeCapacity, FsBlockGhost.diskCapacity⟩

@[reducible] def nativeInvariant (names : Invariant.Names) : InvGS registry :=
  FsBlockGhost.nativeInvariant names

theorem byte_camera_same : nativeCapacity.bytes = FsBlockGhost.machineCapacity.era.disk := rfl
theorem block_cameras_same : nativeCapacity.blocks = FsBlockGhost.nativeCapacity := rfl
theorem byte_slot : nativeCapacity.bytes.image.elem.τ = 12 := rfl
theorem cache_slot : nativeCapacity.blocks.cache.elem.τ = 39 := rfl
theorem dirty_slot : nativeCapacity.blocks.dirty.elem.τ = 40 := rfl
theorem exception_slot : nativeCapacity.blocks.exceptions.elem.τ = 41 := rfl

theorem nativeSpec [InvGS registry] : Spec nativeCapacity := actual nativeCapacity

end MachCSL.Logic.FsBytesBootstrap
