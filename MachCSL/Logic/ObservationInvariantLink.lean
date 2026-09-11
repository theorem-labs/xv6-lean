import MachCSL.Logic.ObservationInvariantProofs
import MachCSL.Logic.InvariantLink

namespace MachCSL.Logic.ObservationInvariant
open Iris Iris.BI MachCSL.Machine

theorem registryObservationInvariantSpec (names : Invariant.Names) :
    letI := names.native Invariant.registryCapacity
    ObservationInvariantSpec Invariant.machineCapacity.power := by
  letI := names.native Invariant.registryCapacity
  exact observationInvariantSpec Invariant.machineCapacity.power

end MachCSL.Logic.ObservationInvariant
