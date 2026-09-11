import MachCSL.Logic.MachineAdequacyProofs
import MachCSL.Logic.UartGhostRegistry

namespace MachCSL.Logic.MachineAdequacy
open Iris Iris.BI Iris.ProgramLogic Iris.ProgramLogic.PrimStep MachCSL.Machine

/-- Exactly the existing native capacity at slots 16–19 in the shared
23-slot registry. No new camera or runtime name is introduced here. -/
@[reducible] def registryPreS : InvGpreS UartGhost.registry :=
  UartGhost.invariantCapacity.preS

theorem registry_not_stuck [Platform] (image : BootImage) (initial : State)
    (off : initial.power = false) (zero : initial.generation = 0) (diskBytes : Nat)
    (template : Era.Record) (N : Namespace)
    (boot : BootInitializer UartGhost.machineCapacity image initial diskBytes template N)
    (n : Nat) (events : List Observation) (threads : List Expr) (finalState : State)
    (steps : PoolSteps image n ([.power], initial) events (threads, finalState)) :
    letI := language image
    (∀ thread ∈ threads, NotStuck (thread, finalState)) ∧ ObservationsOK events finalState := by
  letI := registryPreS
  exact not_stuck UartGhost.machineCapacity image initial off zero diskBytes template N boot
    n events threads finalState steps

/-- Closed camera linkage, conditional only on the explicit client boot
initializer. The concrete machine language and initial disk are unchanged. -/
theorem registry_safe [Platform] (image : BootImage) (initial : State)
    (off : initial.power = false) (zero : initial.generation = 0) (diskBytes : Nat)
    (template : Era.Record) (N : Namespace)
    (boot : BootInitializer UartGhost.machineCapacity image initial diskBytes template N)
    (n : Nat) (events : List Observation) (threads : List Expr) (finalState : State)
    (steps : PoolSteps image n ([.power], initial) events (threads, finalState)) :
    SafeConfiguration image threads finalState events := by
  letI := registryPreS
  exact safe UartGhost.machineCapacity image initial off zero diskBytes template N boot
    n events threads finalState steps

end MachCSL.Logic.MachineAdequacy
