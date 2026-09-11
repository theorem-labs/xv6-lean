import MachCSL.Logic.TsoPinnedStoreProofs
import MachCSL.Logic.TsoStoreLink
import MachCSL.Logic.FsBlockGhostLink

namespace MachCSL.Logic.TsoPinnedStore
open Iris

/-- All subordinate contracts are proved native camera laws. -/
theorem actual {GF : BundledGFunctors} (capacity : Capacity GF) : StoreSpec capacity :=
  storeSpec capacity (TsoStore.nativeContracts capacity)

/-- The existing complete machine heap and TSO capacities, without a new slot. -/
def registryCapacity : Capacity FsBlockGhost.registry :=
  ⟨FsBlockGhost.heapCapacity, FsBlockGhost.eraCapacity.views, FsBlockGhost.eraCapacity.history⟩

theorem heap_same : registryCapacity.heap = FsBlockGhost.machineCapacity.era.heap := rfl
theorem tso_same : registryCapacity.tso = FsBlockGhost.machineCapacity.era.tso := rfl
theorem nativeSpec : StoreSpec registryCapacity := actual registryCapacity

end MachCSL.Logic.TsoPinnedStore
