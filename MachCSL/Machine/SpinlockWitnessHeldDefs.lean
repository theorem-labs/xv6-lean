import MachCSL.Machine.SpinlockWitnessPoolProofs

namespace MachCSL.Machine.SpinlockWitnessHeld
open MachCSL.Memory MachCSL.Machine.SpinlockWitness
open _root_.Sail.ConcurrencyInterfaceV1.Free
attribute [local instance] SpinlockWitness.platform

abbrev WriteRequest := Logic.MemoryWriteWP.WriteRequest
abbrev WriteResult := Logic.MemoryWriteWP.WriteResult

def writeFour : SailM Unit → Option (WriteRequest 4 × (WriteResult → SailM Unit))
  | .impure (.writeMem 4 req) k => some (req, k)
  | _ => none

def writer (program : SailM Unit) : WriteRequest 4 × (WriteResult → SailM Unit) :=
  (writeFour program).getD (SpinlockAccess.writeRequest .lock false 0#32, fun _ => .pure ())

def barrierNext : SailM Unit → Option (_root_.barrier_kind × (Unit → SailM Unit))
  | .impure (.barrier kind) k => some (kind, k)
  | _ => none

def barrier (program : SailM Unit) : _root_.barrier_kind × (Unit → SailM Unit) :=
  (barrierNext program).getD (.Barrier_RISCV_rw_w, fun _ => .pure ())

def swapResult (cpu : Fin 2) (old : BitVec 32) (memory : ByteMap 64) :=
  pauseRun memory 2000 ((readBoundary cpu).2 (.Ok (old, none))) (pausedRegisters cpu)

def swapProgram (cpu : Fin 2) (old : BitVec 32) : SailM Unit :=
  ((swapResult cpu old empty).getD (.pure (), zeroRegisters)).1

def swapResume (cpu : Fin 2) (old : BitVec 32) : WriteResult → SailM Unit :=
  (writer (swapProgram cpu old)).2

def lockMessage : Message 64 := ⟨snapshot SpinlockImage.lockAddress 4 1#32, 0⟩
def counterMessage : Message 64 := ⟨snapshot SpinlockImage.counterAddress 4 1#32, 0⟩
def logOne : WriteLog 64 := [lockMessage]
def logTwo : WriteLog 64 := [lockMessage, counterMessage]
def memoryOne : ByteMap 64 := writeBytes (loadedRam SpinlockImage.image) SpinlockImage.lockAddress 4 1#32
def memoryTwo : ByteMap 64 := writeBytes memoryOne SpinlockImage.counterAddress 4 1#32
def readOne : ByteMap 64 := read (loadedRam SpinlockImage.image) logOne 0 1
def readTwo : ByteMap 64 := read (loadedRam SpinlockImage.image) logTwo 0 1

def prepared (rs : RegisterFile) (next : BitVec 64) : RegisterFile :=
  Sail.Registers.write (Sail.Registers.write rs .minstret_increment true) .nextPC next

def retired (rs : RegisterFile) (pc : BitVec 64) (count : Nat) : RegisterFile :=
  Sail.Registers.write (Sail.Registers.write rs .PC pc) .minstret (BitVec.ofNat 64 count)

def acquiredRegisters : RegisterFile :=
  retired (Sail.Registers.write (pausedRegisters 0) .x15 0#64) 0x80000020#64 8

/-- Boundaries after successful AMO: ADDIW old, non-taken retry branch,
counter load, and modular counter increment. -/
def workAfter : Nat → RegisterFile
  | 0 => acquiredRegisters
  | n + 1 =>
    let pc := BitVec.ofNat 64 (0x80000000 + 4 * (n + 9))
    let rs := prepared (workAfter n) pc
    let next := match n with
      | 0 => Sail.Registers.write rs .x15 0#64
      | 1 => rs
      | 2 => Sail.Registers.write rs .x16 0#64
      | _ => Sail.Registers.write rs .x16 1#64
    retired next pc (n + 9)

def counterRegisters : RegisterFile := prepared (workAfter 4) 0x80000034#64
def counterResult := pauseRun readOne 2000 (cycle false) (workAfter 4)
def counterProgram : SailM Unit := (counterResult.getD (.pure (), zeroRegisters)).1
def counterResume : WriteResult → SailM Unit := (writer counterProgram).2

def storedRegisters : RegisterFile := retired counterRegisters 0x80000034#64 13
def fenceRegisters : RegisterFile := prepared storedRegisters 0x80000038#64
def fenceResult := pauseRun readTwo 2000 (cycle false) storedRegisters
def fenceProgram : SailM Unit := (fenceResult.getD (.pure (), zeroRegisters)).1
def fenceResume : Unit → SailM Unit := (barrier fenceProgram).2

def fencedRegisters : RegisterFile := retired fenceRegisters 0x80000038#64 14
def unlockRegisters : RegisterFile := prepared fencedRegisters 0x8000003c#64
def unlockResult := pauseRun readTwo 2000 (cycle false) fencedRegisters
def unlockProgram : SailM Unit := (unlockResult.getD (.pure (), zeroRegisters)).1
def unlockResume : WriteResult → SailM Unit := (writer unlockProgram).2

end MachCSL.Machine.SpinlockWitnessHeld
