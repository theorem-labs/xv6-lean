import MachCSL.Logic.FsBootBytesProofs
import MachCSL.Logic.FsBytesBootstrapLink

namespace MachCSL.Logic.FsBootBytes
open Iris

abbrev registry := FsBlockGhost.registry

def nativeCapacity : Capacity registry := FsBytesBootstrap.nativeCapacity

@[reducible] def nativeInvariant (names : Invariant.Names) : InvGS registry :=
  FsBlockGhost.nativeInvariant names

theorem physical_byte_same : nativeCapacity.bytes = FsBlockGhost.machineCapacity.era.disk := rfl
theorem block_cameras_same : nativeCapacity.blocks = FsBlockGhost.nativeCapacity := rfl
theorem byte_slot : nativeCapacity.bytes.image.elem.τ = 12 := rfl

theorem nativeCarveSpec : CarveSpec nativeCapacity := carveSpec nativeCapacity

theorem nativeSpec [InvGS registry] : Spec nativeCapacity := actual nativeCapacity

end MachCSL.Logic.FsBootBytes
