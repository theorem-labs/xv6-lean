import MachCSL.Logic.TsoStoreProofs
import MachCSL.Logic.TsoViewsProofs
import MachCSL.Logic.TsoHistoryProofs
import MachCSL.Logic.FsLinkRegistry

namespace MachCSL.Logic.TsoStore
open Iris

/-- Every callee contract is discharged by the existing native camera laws. -/
theorem nativeContracts {GF : BundledGFunctors} (capacity : Capacity GF) : Contracts capacity where
  views := Tso.Views.viewsSpec capacity.views
  history := Tso.History.historySpec capacity.history
  logGrow := Tso.Views.natAuth_update capacity.views

theorem nativeStoreSpec {GF : BundledGFunctors} (capacity : Capacity GF) : StoreSpec capacity :=
  storeSpec capacity (nativeContracts capacity)

/-- No new functor slots: byte/timestamp 0/1, views/length 2/3, history 4/5,
and the full heap's metadata indirection and values 13/14. -/
def registryCapacity : Capacity FsLink.registry :=
  ⟨FsLink.heapCapacity, FsLink.eraCapacity.views, FsLink.eraCapacity.history⟩

theorem registry_heap_same : registryCapacity.heap = FsLink.machineCapacity.era.heap := rfl
theorem registry_tso_same : registryCapacity.tso = FsLink.machineCapacity.era.tso := rfl

theorem registryStoreSpec : StoreSpec registryCapacity := nativeStoreSpec registryCapacity

end MachCSL.Logic.TsoStore
