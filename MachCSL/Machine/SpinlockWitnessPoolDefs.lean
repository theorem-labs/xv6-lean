import MachCSL.Machine.SpinlockWitnessDefs

namespace MachCSL.Machine.SpinlockWitness
open MachCSL.Memory

def cpuId (cpu : Fin 2) : CPU := ⟨cpu.val, by have := cpu.isLt; omega⟩

def bootLocal (cpu : Fin 2) (devices : Devices.State) : LocalState Devices.State where
  registers := bootRegisters SpinlockImage.image.vector (BitVec.ofNat 64 cpu.val)
  memory := loadedRam SpinlockImage.image
  devices := devices
  log := []
  view := 0
  reservation := none

def pausedLocal (cpu : Fin 2) (devices : Devices.State) : LocalState Devices.State :=
  { bootLocal cpu devices with registers := (paused cpu).2 }

def firstPaused (before : State) : State :=
  writeBack (bootState SpinlockImage.image before) 0 (pausedLocal 0 (Devices.reset before.devices))

def bothPaused (before : State) : State :=
  writeBack (firstPaused before) 1 (pausedLocal 1 (Devices.reset before.devices))

def zeroSnapshot : Reservation := snapshot SpinlockImage.lockAddress 4 0#32

def reservedLocal (before : State) : LocalState Devices.State :=
  { focus (bothPaused before) 0 with reservation := some zeroSnapshot }

/-- CPU zero has consumed the actual exclusive-read event; CPU one's program
still contains its distinct, exact unread continuation. -/
def afterReadZero (before : State) : State :=
  writeBack (bothPaused before) 0 (reservedLocal before)

def tailWorkers (generation : Nat) : List Expr := (powerFork generation).drop 2

def bothPausedPool (generation : Nat) : List Expr :=
  [.power, .hart generation 0 (paused 0).1, .hart generation 1 (paused 1).1] ++
    tailWorkers generation

def conflictPool (generation : Nat) : List Expr :=
  [.power, .hart generation 0 ((readBoundary 0).2 (.Ok (0#32, none))),
    .hart generation 1 (paused 1).1] ++ tailWorkers generation

end MachCSL.Machine.SpinlockWitness
