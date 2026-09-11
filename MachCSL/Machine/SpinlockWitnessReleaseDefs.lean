import MachCSL.Machine.SpinlockWitnessHeldPoolProofs

namespace MachCSL.Machine.SpinlockWitnessRelease
open MachCSL.Memory MachCSL.Machine.SpinlockWitness
open MachCSL.Machine.SpinlockWitnessHeld
attribute [local instance] SpinlockWitness.platform

def failedMessage : Message 64 := ⟨snapshot SpinlockImage.lockAddress 4 1#32, 1⟩
def releaseZeroMessage : Message 64 := ⟨snapshot SpinlockImage.lockAddress 4 0#32, 0⟩
def winMessage : Message 64 := ⟨snapshot SpinlockImage.lockAddress 4 1#32, 1⟩
def incrementMessage : Message 64 := ⟨snapshot SpinlockImage.counterAddress 4 2#32, 1⟩
def releaseOneMessage : Message 64 := ⟨snapshot SpinlockImage.lockAddress 4 0#32, 1⟩
def logThree := logTwo ++ [failedMessage]
def logFour := logThree ++ [releaseZeroMessage]
def logFive := logFour ++ [winMessage]
def logSix := logFive ++ [incrementMessage]
def logSeven := logSix ++ [releaseOneMessage]
def memoryThree := writeBytes memoryTwo SpinlockImage.lockAddress 4 1#32
def memoryFour := writeBytes memoryThree SpinlockImage.lockAddress 4 0#32
def memoryFive := writeBytes memoryFour SpinlockImage.lockAddress 4 1#32
def memorySix := writeBytes memoryFive SpinlockImage.counterAddress 4 2#32
def memorySeven := writeBytes memorySix SpinlockImage.lockAddress 4 0#32

def readFourView := read (loadedRam SpinlockImage.image) logFour 1 3
def readFiveView := read (loadedRam SpinlockImage.image) logFive 1 5
def readSixView := read (loadedRam SpinlockImage.image) logSix 1 5

def failedRegisters : RegisterFile :=
  retired (Sail.Registers.write (pausedRegisters 1) .x15 1#64) 0x80000020#64 8

def retryAfter : Nat → RegisterFile
  | 0 => failedRegisters
  | n + 1 =>
    let pc := if n = 0 then 0x80000024#64 else if n = 1 then 0x80000018#64 else 0x8000001c#64
    let rs := prepared (retryAfter n) (if n = 1 then 0x80000028#64 else pc)
    let next := if n = 1 then Sail.Registers.write rs .nextPC pc else Sail.Registers.write rs .x15 1#64
    retired next pc (n + 9)

def retryRegisters := prepared (retryAfter 3) 0x80000020#64
def retryResult := pauseRun readFourView 2000 (cycle false) (retryAfter 3)
def retryProgram : SailM Unit := (retryResult.getD (.pure (), zeroRegisters)).1

def reader (program : SailM Unit) : ReadRequest 4 × (ReadResult 4 → SailM Unit) :=
  (readFour program).getD (SpinlockAccess.readRequest .lock true, fun _ => .pure ())
def retryResume := (reader retryProgram).2

def winResult (memory : ByteMap 64) := pauseRun memory 2000
  (retryResume (.Ok (0#32, none))) retryRegisters
def winProgram : SailM Unit := ((winResult empty).getD (.pure (), zeroRegisters)).1
def winResume := (writer winProgram).2

def wonRegisters : RegisterFile :=
  retired (Sail.Registers.write retryRegisters .x15 0#64) 0x80000020#64 12

def secondWork : Nat → RegisterFile
  | 0 => wonRegisters
  | n + 1 =>
    let pc := BitVec.ofNat 64 (0x80000000 + 4 * (n + 9))
    let rs := prepared (secondWork n) pc
    let next := match n with
      | 0 => Sail.Registers.write rs .x15 0#64
      | 1 => rs
      | 2 => Sail.Registers.write rs .x16 1#64
      | _ => Sail.Registers.write rs .x16 2#64
    retired next pc (n + 13)

def incrementRegisters := prepared (secondWork 4) 0x80000034#64
def incrementResult := pauseRun readFiveView 2000 (cycle false) (secondWork 4)
def incrementProgram : SailM Unit := (incrementResult.getD (.pure (), zeroRegisters)).1
def incrementResume := (writer incrementProgram).2

def incrementedRegisters := retired incrementRegisters 0x80000034#64 17
def secondFenceRegisters := prepared incrementedRegisters 0x80000038#64
def secondFenceResult := pauseRun readSixView 2000 (cycle false) incrementedRegisters
def secondFenceProgram : SailM Unit := (secondFenceResult.getD (.pure (), zeroRegisters)).1
def secondFenceResume := (barrier secondFenceProgram).2

def secondFencedRegisters := retired secondFenceRegisters 0x80000038#64 18
def releaseRegisters := prepared secondFencedRegisters 0x8000003c#64
def releaseResult := pauseRun readSixView 2000 (cycle false) secondFencedRegisters
def releaseProgram : SailM Unit := (releaseResult.getD (.pure (), zeroRegisters)).1
def releaseResume := (writer releaseProgram).2

end MachCSL.Machine.SpinlockWitnessRelease
