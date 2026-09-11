import MachCSL.Logic.JalMachineSafetyProofs
import MachCSL.Logic.JalBootHandlerLink
import MachCSL.Machine.FetchIntegration

namespace MachCSL.Logic.JalMachineSafety
open Iris Iris.BI MachCSL.Machine

/-- All worker specifications are discharged by the actual linked handler.
This holds for every represented prefix of the actual initial durable disk. -/
theorem boot_initializer [Platform] (initial : State) (diskBytes : Nat) :
    MachineAdequacy.BootInitializer UartGhost.machineCapacity jalImage initial
      diskBytes template namespaces.observations := by
  apply initializer_of_boot_handler initial diskBytes
  intro native fixed whole
  letI := native
  exact JalBootHandler.registry_boot_handler namespaces fixed whole template

/-- Closed native adequacy for all finite actual schedules of the JAL image.
No ghost-state, boot-handler, worker-WP, or initial-register premise remains. -/
theorem safe_sized [Platform] (initial : State)
    (off : initial.power = false) (zero : initial.generation = 0) (diskBytes : Nat)
    (n : Nat) (events : List Observation) (threads : List Expr) (finalState : State)
    (steps : PoolSteps jalImage n ([.power], initial) events (threads, finalState)) :
    MachineAdequacy.SafeConfiguration jalImage threads finalState events :=
  MachineAdequacy.registry_safe jalImage initial off zero diskBytes template
    namespaces.observations (boot_initializer initial diskBytes) n events threads finalState steps

/-- Disk size is internal proof bookkeeping for this safety-only client.
The machine's physical initial disk and all its transitions are unchanged. -/
theorem safe [Platform] (initial : State)
    (off : initial.power = false) (zero : initial.generation = 0)
    (n : Nat) (events : List Observation) (threads : List Expr) (finalState : State)
    (steps : PoolSteps jalImage n ([.power], initial) events (threads, finalState)) :
    MachineAdequacy.SafeConfiguration jalImage threads finalState events :=
  safe_sized initial off zero 0 n events threads finalState steps

/-- A positive actual schedule powers on, fetches and retires JAL on hart zero,
and reaches a safe twelve-thread pool. The medium is the original initial disk.
This witness selects one permitted boot; `safe` covers every permitted boot. -/
theorem positive_fetched_execution [Platform] (initial : State)
    (off : initial.power = false) (zero : initial.generation = 0) :
    ∃ n, 1 < n ∧
      PoolSteps jalImage n ([.power], initial) [.powerOn]
        (.power :: powerFork initial.generation, fetchedJalState initial) ∧
      MachineAdequacy.SafeConfiguration jalImage
        (.power :: powerFork initial.generation) (fetchedJalState initial) [.powerOn] ∧
      (fetchedJalState initial).devices.virtio.v_disk = initial.devices.virtio.v_disk := by
  obtain ⟨n, positive, steps⟩ := powerOn_fetchedJal initial off
  exact ⟨n, positive, steps, safe initial off zero n [.powerOn] _ _ steps,
    powerOn_fetchedJal_disk initial⟩

/-- The gate's initial conditions are inhabited for every actual device state,
and the positive fetched execution is safe without an initial-state premise. -/
theorem initialState_positive_execution [Platform] (devices : Devices.State) :
    ∃ n, 1 < n ∧
      PoolSteps jalImage n ([.power], initialState devices) [.powerOn]
        (.power :: powerFork 0, fetchedJalState (initialState devices)) ∧
      MachineAdequacy.SafeConfiguration jalImage
        (.power :: powerFork 0) (fetchedJalState (initialState devices)) [.powerOn] ∧
      (fetchedJalState (initialState devices)).devices.virtio.v_disk = devices.virtio.v_disk :=
  positive_fetched_execution (initialState devices) rfl rfl

/-- Fully concrete nonvacuity witness: platform predicates, initial state, and
positive actual execution are supplied, with no remaining premise. -/
theorem concrete_positive_execution :
    letI := examplePlatform
    ∃ n, 1 < n ∧
      PoolSteps jalImage n ([.power], initialState Devices.initial) [.powerOn]
        (.power :: powerFork 0, fetchedJalState (initialState Devices.initial)) ∧
      MachineAdequacy.SafeConfiguration jalImage
        (.power :: powerFork 0) (fetchedJalState (initialState Devices.initial)) [.powerOn] ∧
      (fetchedJalState (initialState Devices.initial)).devices.virtio.v_disk =
        Devices.initial.virtio.v_disk := by
  letI := examplePlatform
  exact initialState_positive_execution Devices.initial

end MachCSL.Logic.JalMachineSafety
