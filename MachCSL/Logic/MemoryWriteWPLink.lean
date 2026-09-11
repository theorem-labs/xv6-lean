import MachCSL.Logic.MemoryWriteWPProofs
import MachCSL.Logic.TsoStoreLink
import MachCSL.Logic.MemoryExclusiveWPProofs
import MachCSL.Logic.ReservationProofs

namespace MachCSL.Logic.MemoryWriteWP
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

/-- Every primitive contract is discharged by its existing native proof. -/
theorem nativeContracts {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : Contracts capacity where
  store := TsoStore.nativeStoreSpec (storeCapacity capacity)
  views := Tso.Views.viewsSpec capacity.era.views
  reservations := Reservations.reservationSpec capacity.era.reservations
  exclusive := MemoryExclusiveWP.memoryExclusiveWPSpec capacity

theorem nativeMemoryWriteWPSpec {GF : BundledGFunctors} [Platform] {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : MachineInterp.Capacity GF) : MemoryWriteWPSpec capacity :=
  memoryWriteWPSpec capacity (nativeContracts capacity)

/-- Same complete machine registry, with no new camera or runtime ghost name. -/
theorem registryMemoryWriteWPSpec [Platform] (names : Invariant.Names) :
    letI := FsLink.nativeInvariant names
    MemoryWriteWPSpec FsLink.machineCapacity := by
  letI := FsLink.nativeInvariant names
  exact nativeMemoryWriteWPSpec FsLink.machineCapacity

end MachCSL.Logic.MemoryWriteWP
