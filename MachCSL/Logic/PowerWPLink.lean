import MachCSL.Logic.PowerWPProofs
import MachCSL.Logic.InvariantLink

namespace MachCSL.Logic.PowerWP
open Iris Iris.BI MachCSL.Machine

theorem registryPowerWPSpec [Platform] (names : Invariant.Names) :
    letI := names.native Invariant.registryCapacity
    PowerWPSpec Invariant.machineCapacity := by
  letI := names.native Invariant.registryCapacity
  exact powerWPSpec Invariant.machineCapacity

/-- The native registry discharges resource allocation and transition proofs;
the full eleven-thread boot handler remains an explicit client obligation. -/
theorem registry_wp_power [Platform] (names : Invariant.Names)
    (image : BootImage) (fixed : MachineInterp.FixedNames) (whole : List Observation)
    (template : Era.Record) (N : Namespace) (post : Empty → IProp Invariant.registry) :
    letI := names.native Invariant.registryCapacity
    iprop(⊢ ObservationInvariant.trivial Invariant.machineCapacity.power N fixed.observations -∗
      bootHandler Invariant.machineCapacity image fixed whole template -∗
      DeadThread.threadWP Invariant.machineCapacity image fixed whole .power post) := by
  letI := names.native Invariant.registryCapacity
  exact wp_power Invariant.machineCapacity image fixed whole template N post

end MachCSL.Logic.PowerWP
