import MachCSL.Logic.IcacheRegionInvariantProofs
import MachCSL.Logic.FsBlockGhostLink

namespace MachCSL.Logic.IcacheRegionInvariant
open Iris

/-- Uses the existing registry through slot 41; no camera is added or replaced. -/
abbrev registry := FsBlockGhost.registry

def nativeCapacity : Capacity registry :=
  ⟨⟨FsBlockGhost.referenceCapacity, FsBlockGhost.couplingCapacity,
      FsBlockGhost.typeCapacity, FsBlockGhost.transactionCapacity,
      FsBlockGhost.recordCapacity, FsBlockGhost.linkCapacity,
      FsBlockGhost.topCapacity, FsBlockGhost.epochCapacity,
      FsBlockGhost.registryCapacity⟩,
    FsBlockGhost.nativeCapacity, FsBlockGhost.diskCapacity,
    FsBlockGhost.topRegistryCapacity.arms⟩

@[reducible] def nativeInvariant (names : Invariant.Names) : InvGS registry :=
  FsBlockGhost.nativeInvariant names

theorem native_bytes_same : (byteCapacity nativeCapacity).bytes = FsBlockGhost.machineCapacity.era.disk := rfl
theorem native_blocks_same : (byteCapacity nativeCapacity).blocks = FsBlockGhost.nativeCapacity := rfl
theorem native_top_same : topCapacity nativeCapacity = FsBlockGhost.topRegistryCapacity := rfl
theorem native_transactions_same : nativeCapacity.region.transactions = FsBlockGhost.transactionCapacity := rfl
theorem native_records_same : nativeCapacity.region.records = FsBlockGhost.recordCapacity := rfl

theorem nativeSpec [InvGS registry] : Spec nativeCapacity := actual nativeCapacity

end MachCSL.Logic.IcacheRegionInvariant
