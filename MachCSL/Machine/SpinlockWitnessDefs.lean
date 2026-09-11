import MachCSL.Machine.SpinlockWitnessRun
import MachCSL.Machine.SpinlockAccessDefs
import MachCSL.Machine.FetchIntegration

namespace MachCSL.Machine.SpinlockWitness
open _root_.Sail.ConcurrencyInterfaceV1.Free

/-- Concrete platform parameters for an existential execution witness. -/
@[reducible] def platform : Platform where
  match_reservation := fun _ => false
  valid_reservation := fun _ => false

attribute [local instance] platform

def setupRun (cpu : Fin 2) (rounds : Nat) : Option RegisterFile :=
  cyclesRun (loadedRam SpinlockImage.image) 2000
    (bootRegisters SpinlockImage.image.vector (BitVec.ofNat 64 cpu.val)) rounds

/-- Compact expected files at setup boundaries. Per-cycle kernel certificates
check these exact dependent-file updates against actual fetched execution. -/
def setupAfter (cpu : Fin 2) : Nat → RegisterFile
  | 0 => bootRegisters SpinlockImage.image.vector (BitVec.ofNat 64 cpu.val)
  | n + 1 =>
    let started := Sail.Registers.write (setupAfter cpu n) .minstret_increment true
    let pc := BitVec.ofNat 64 (0x80000000 + 4 * (n + 1))
    let prepared := Sail.Registers.write started .nextPC pc
    let executed := match n with
      | 0 => Sail.Registers.write prepared .x5 (BitVec.ofNat 64 cpu.val)
      | 1 => Sail.Registers.write prepared .x6 1#64
      | 2 => prepared
      | 3 => Sail.Registers.write prepared .x10 0x8000100c#64
      | 4 => Sail.Registers.write prepared .x10 0x80001000#64
      | 5 => Sail.Registers.write prepared .x14 1#64
      | _ => Sail.Registers.write prepared .x15 1#64
    Sail.Registers.write (Sail.Registers.write executed .PC pc) .minstret (BitVec.ofNat 64 (n + 1))

def setupRegisters (cpu : Fin 2) : RegisterFile := setupAfter cpu 7

def prefixResult (cpu : Fin 2) : Option (SailM Unit × RegisterFile) :=
  pauseRun (loadedRam SpinlockImage.image) 2000 (cycle false) (setupRegisters cpu)

def pausedProgram (cpu : Fin 2) : SailM Unit :=
  ((prefixResult cpu).getD (.pure (), zeroRegisters)).1

/-- Before the AMO read, the cycle has enabled retirement and prepared nextPC;
the read has not yet returned a value or modified a destination register. -/
def pausedRegisters (cpu : Fin 2) : RegisterFile :=
  Sail.Registers.write (Sail.Registers.write (setupRegisters cpu) .minstret_increment true)
    .nextPC 0x80000020#64

def paused (cpu : Fin 2) : SailM Unit × RegisterFile :=
  (pausedProgram cpu, pausedRegisters cpu)

abbrev ReadRequest := Logic.MemoryReadWP.ReadRequest
abbrev ReadResult := Logic.MemoryReadWP.ReadResult

/-- Extract the exact continuation only when the residual program is a
four-byte memory-read event. Other pauses cannot satisfy this classifier. -/
def readFour : SailM Unit → Option (ReadRequest 4 × (ReadResult 4 → SailM Unit))
  | .impure (.readMem 4 req) k => some (req, k)
  | _ => none

def readBoundary (cpu : Fin 2) : ReadRequest 4 × (ReadResult 4 → SailM Unit) :=
  (readFour (paused cpu).1).getD (SpinlockAccess.readRequest .lock true, fun _ => .pure ())

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

end MachCSL.Machine.SpinlockWitness
