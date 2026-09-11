import MachCSL.Logic.FsBootRecoveryProofs
import MachCSL.Logic.FsBootBytesLink

namespace MachCSL.Logic.FsBootRecovery
open Iris

abbrev registry := FsBlockGhost.registry

def nativeCapacity : Capacity registry := ⟨FsBlockGhost.eraCapacity, FsBlockGhost.nativeCapacity⟩

@[reducible] def nativeInvariant (names : Invariant.Names) : InvGS registry :=
  FsBlockGhost.nativeInvariant names

theorem byte_capacity_same : nativeCapacity.bytes = FsBootBytes.nativeCapacity := rfl
theorem era_capacity_same : nativeCapacity.era = FsBlockGhost.machineCapacity.era := rfl
theorem physical_name template era : (forEra template era).img = era.disk := rfl

theorem nativeClientSpec : ClientSpec nativeCapacity := clientSpec nativeCapacity

theorem nativeSpec [InvGS registry] : Spec nativeCapacity := actual nativeCapacity

end MachCSL.Logic.FsBootRecovery
