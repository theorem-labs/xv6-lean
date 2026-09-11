import MachCSL.Logic.FsBytesInvariantRowsProofs
import MachCSL.Logic.FsBlockGhostLink

namespace MachCSL.Logic.FsBytesInvariant
open Iris

/-- The source invariant uses existing block cameras and the very same signed
byte camera as the physical disk, at a separately supplied logged-view name. -/
def nativeCapacity : Capacity FsBlockGhost.registry :=
  ⟨FsBlockGhost.nativeCapacity, FsBlockGhost.diskCapacity⟩
theorem bytes_machine_same : nativeCapacity.bytes = FsBlockGhost.machineCapacity.era.disk := rfl
theorem cache_slot : nativeCapacity.blocks.cache.elem.τ = 39 := rfl
theorem exceptions_slot : nativeCapacity.blocks.exceptions.elem.τ = 41 := rfl
theorem bytes_slot : nativeCapacity.bytes.image.elem.τ = 12 := rfl
theorem nativeSpec [InvGS FsBlockGhost.registry] : Spec nativeCapacity := actual nativeCapacity

end MachCSL.Logic.FsBytesInvariant
