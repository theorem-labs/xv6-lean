import MachCSL.Machine.SpinlockWitnessHeldDefs

namespace MachCSL.Machine.SpinlockWitnessHeld
open MachCSL.Memory MachCSL.Machine.SpinlockWitness

def localAt (rs : RegisterFile) (memory : ByteMap 64) (log : WriteLog 64)
    (view : Nat) (reservation : Option Reservation) (devices : Devices.State) :
    LocalState Devices.State := ⟨rs, memory, devices, log, view, reservation⟩

def swapLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (pausedRegisters 0) memoryOne logOne 1 none devices

def counterLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt counterRegisters memoryOne logOne 1 none devices

def committedLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt counterRegisters memoryTwo logTwo 1 none devices

def oneSnapshot : Reservation := snapshot SpinlockImage.lockAddress 4 1#32

def readerLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (pausedRegisters 1) memoryTwo logTwo 2 (some oneSnapshot) devices

def unlockLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt unlockRegisters memoryTwo logTwo 1 none devices

def swapped (before : State) : State :=
  writeBack (afterReadZero before) 0 (swapLocal (Devices.reset before.devices))

def counterReady (before : State) : State :=
  writeBack (swapped before) 0 (counterLocal (Devices.reset before.devices))

def counterCommitted (before : State) : State :=
  writeBack (counterReady before) 0 (committedLocal (Devices.reset before.devices))

def oneReserved (before : State) : State :=
  writeBack (counterCommitted before) 1 (readerLocal (Devices.reset before.devices))

def unlockReady (before : State) : State :=
  writeBack (oneReserved before) 0 (unlockLocal (Devices.reset before.devices))

def pairPool (generation : Nat) (cpu0 cpu1 : SailM Unit) : List Expr :=
  [.power, .hart generation 0 cpu0, .hart generation 1 cpu1] ++ tailWorkers generation

def blockedPool (generation : Nat) : List Expr :=
  pairPool generation unlockProgram (swapProgram 1 1#32)

end MachCSL.Machine.SpinlockWitnessHeld
