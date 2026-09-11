import MachCSL.Logic.SpinlockBootHandlerLink
import MachCSL.Logic.JalMachineSafetyDefs
import MachCSL.Logic.MachineAdequacyProofs

namespace MachCSL.Logic.SpinlockMachineSafety
open Iris Iris.BI MachCSL.Machine

/-- Reuse the established device/observation namespaces; the lock is a sibling. -/
def namespaces : JalBootHandler.Namespaces := JalMachineSafety.namespaces
def lockNamespace : Namespace := nroot.@(4 : Nat)
def template : Era.Record := JalMachineSafety.template
def initialState (devices : Devices.State) : State := JalMachineSafety.initialState devices

theorem boot_initializer [Platform] (initial : State) (diskBytes : Nat) :
    MachineAdequacy.BootInitializer FsTop.machineCapacity SpinlockImage.image initial
      diskBytes template namespaces.observations := by
  apply MachineAdequacy.initializer_of_handler FsTop.machineCapacity SpinlockImage.image initial
    diskBytes template namespaces.observations
  intro native fixed whole
  letI := native
  exact SpinlockBootHandler.registry_boot_handler namespaces lockNamespace fixed whole template

/-- Native safety for every finite actual schedule, including every permitted
boot, all eight CPUs, devices, stale generations and power transitions. This is
the safety conjunct of the gate; holder exclusion and a witness are separate. -/
theorem safe_sized [Platform] (initial : State)
    (off : initial.power = false) (zero : initial.generation = 0) (diskBytes : Nat)
    (n : Nat) (events : List Observation) (threads : List Expr) (finalState : State)
    (steps : PoolSteps SpinlockImage.image n ([.power], initial) events (threads, finalState)) :
    MachineAdequacy.SafeConfiguration SpinlockImage.image threads finalState events := by
  letI := FsTop.invariantCapacity.preS
  exact MachineAdequacy.safe FsTop.machineCapacity SpinlockImage.image initial off zero
    diskBytes template namespaces.observations (boot_initializer initial diskBytes)
    n events threads finalState steps

/-- Disk bookkeeping does not restrict the machine's complete durable medium. -/
theorem safe [Platform] (initial : State)
    (off : initial.power = false) (zero : initial.generation = 0)
    (n : Nat) (events : List Observation) (threads : List Expr) (finalState : State)
    (steps : PoolSteps SpinlockImage.image n ([.power], initial) events (threads, finalState)) :
    MachineAdequacy.SafeConfiguration SpinlockImage.image threads finalState events :=
  safe_sized initial off zero 0 n events threads finalState steps

theorem initial_safe [Platform] (devices : Devices.State)
    (n : Nat) (events : List Observation) (threads : List Expr) (finalState : State)
    (steps : PoolSteps SpinlockImage.image n ([.power], initialState devices) events (threads, finalState)) :
    MachineAdequacy.SafeConfiguration SpinlockImage.image threads finalState events :=
  safe (initialState devices) rfl rfl n events threads finalState steps

end MachCSL.Logic.SpinlockMachineSafety
