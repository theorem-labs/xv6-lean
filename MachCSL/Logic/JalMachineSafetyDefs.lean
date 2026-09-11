import MachCSL.Logic.JalBootHandlerDefs

/-! Concrete data for the fetched-JAL machine gate. Ghost names in `template`
are auxiliary data, not allocated resources; boot allocation supplies the actual
machine names and memory image. -/
namespace MachCSL.Logic.JalMachineSafety
open Iris MachCSL.Machine

/-- An inhabitant of the two source platform-predicate parameters. The main
safety theorem remains universally quantified over the platform. -/
@[reducible] def examplePlatform : Platform where
  match_reservation := fun _ => false
  valid_reservation := fun _ => false

def namespaces : JalBootHandler.Namespaces where
  observations := nroot.@(0 : Nat)
  uart := nroot.@(1 : Nat)
  plic := nroot.@(2 : Nat)
  wires := nroot.@(3 : Nat)
  uart_observations := by
    intro p present
    apply CoPset.in_diff.mpr
    exact ⟨CoPset.mem_full, fun other =>
      ndot_ne_disjoint nroot (show (0 : Nat) ≠ 1 by decide) p ⟨present, other⟩⟩

def template : Era.Record where
  registers := fun _ => 0
  heap := 0
  metadata := 0
  uart := 0
  plic := 0
  virtio := 0
  kernelMap := 0
  kernelPageTable := 0
  kernelPageTableBound := 0
  supervisorTranslation := fun _ => 0
  supervisorInterruptEnable := fun _ => 0
  supervisorPreviousPrivilege := fun _ => 0
  supervisorPreviousInterruptEnable := fun _ => 0
  parkedHart := fun _ => 0
  processState := fun _ => 0
  disk := 0
  logMirror := 0
  heldLocks := fun _ => 0
  reservations := 0
  timestamps := 0
  logEntries := 0
  logLength := 0
  views := 0
  image := ∅

/-- A concrete witness for the powered-off initial-state conditions. The caller
supplies the actual device state, including its complete durable medium. -/
def initialState (devices : Devices.State) : State where
  registers := fun _ => zeroRegisters
  memory := Memory.empty
  devices := devices
  generation := 0
  power := false
  reservations := fun _ => none
  image := Memory.empty
  log := []
  views := fun _ => 0

end MachCSL.Logic.JalMachineSafety
