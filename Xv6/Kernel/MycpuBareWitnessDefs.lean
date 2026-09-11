import Xv6.Kernel.MycpuBareResultProofs
import Xv6.Kernel.MycpuFetchBytesProofs
import MachCSL.Machine.SpinlockWitnessRun
import MachCSL.Machine.FetchIntegration

namespace Xv6.Kernel.MycpuBareWitness
open MachCSL MachCSL.Machine MachCSL.Memory LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free

@[reducible] def platform : Platform where
  match_reservation := fun _ => false
  valid_reservation := fun _ => false
attribute [local instance] platform

def cpu : CPU := 3

def entry (r : Register) : RegisterType r :=
  match r with
  | .PC | .nextPC => 0x800018ba#64
  | .x1 => 0x80000100#64
  | .x2 => 0x80040000#64
  | .x4 => 3#64
  | .x8 => 0x123456789abcdef0#64
  | .cur_privilege => .Supervisor
  | .hart_state => .HART_ACTIVE ()
  | .misa => 0x800000000014112d#64
  | .menvcfg => 0xa000000000000000#64
  | .mstatus => 0xa00000000#64
  | .pmpcfg_n => Vector.replicate 64 0x0f#8
  | .pmpaddr_n => Vector.replicate 64 0x22000000#64
  | .pma_regions => pmaBoot
  | r => zeroRegisters r

def image : ByteMap 64 := loadedRam Xv6.Machine.bootImage

/-- A checked read cache, with the actual image as its total fallback. -/
def cachedImage (a : PhysicalAddress) : Option Byte :=
  if h : 0x800018ba ≤ a.toNat ∧ a.toNat < 0x800018ba + 34 then
    some (Xv6.Machine.byteOfUInt8 (MycpuFetchBytes.bytes[a.toNat - 0x800018ba]'(by
      change a.toNat - 0x800018ba < 34; omega)))
  else if 0x80000000 + 41632 ≤ a.toNat ∧ a.toNat < ramHigh then some 0
  else image a

def initial : LocalState Devices.State :=
  ⟨entry, image, Devices.initial, [], 0, none⟩

def storeState (s : LocalState Devices.State)
    (req : MachCSL.Logic.MemoryWriteWP.WriteRequest n) (word : BitVec (8*n)) :
    LocalState Devices.State :=
  { s with memory := writeBytes s.memory req.pa n word
           log := s.log ++ [⟨snapshot req.pa n word, hartAgent cpu⟩]
           reservation := none }

/-- Pause on each genuine unsupported event; accept only an ordinary RAM write.
The inner evaluator supplies all register and RAM-read transitions. -/
def run : Nat → SailM Unit → LocalState Devices.State → Option (LocalState Devices.State)
  | 0, _, _ => none
  | fuel + 1, program, s => do
    let (rest, regs) ← SpinlockWitness.pauseRun
      (Memory.read cachedImage s.log (hartAgent cpu) s.view) 2000 program s.registers
    let t := { s with registers := regs }
    match rest with
    | .pure _ => some t
    | .impure (.writeMem _ req) k =>
      if deviceAddress req.pa || accessExclusive req.access_kind then none else
      match req.value with
      | none => none
      | some word => run fuel (k (.Ok none)) (storeState t req word)
    | _ => none

termination_by structural fuel _ _ => fuel

/-- An exact counter-indexed sequence of completed generated cycles. -/
inductive Cycles : Nat → LocalState Devices.State → LocalState Devices.State → Prop
  | nil (s) : Cycles 0 s s
  | cons {n s t u} :
      NodeSteps Devices.bus (fun _ => False) (hartAgent cpu) image
        (cycle false) { s with reservation := none } (.pure ()) t →
      Cycles n t u → Cycles (n+1) s u

def checkpoint (k : Nat) : RegisterFile :=
  Sail.Registers.write (MycpuBare.reference entry k) .minstret (BitVec.ofNat 64 k)

def logAt (k : Nat) : WriteLog 64 :=
  (if 1 < k then [⟨snapshot (MycpuBare.raSlot entry) 8 (entry .x1), hartAgent cpu⟩] else []) ++
  (if 2 < k then [⟨snapshot (MycpuBare.s0Slot entry) 8 (entry .x8), hartAgent cpu⟩] else [])

def memoryAt (k : Nat) : ByteMap 64 :=
  let first := if 1 < k then writeBytes image (MycpuBare.raSlot entry) 8 (entry .x1) else image
  if 2 < k then writeBytes first (MycpuBare.s0Slot entry) 8 (entry .x8) else first

def stateAt (k : Nat) : LocalState Devices.State :=
  ⟨checkpoint k, memoryAt k, Devices.initial, logAt k, 0, none⟩

def configured : State where
  registers := updateHart (fun _ => zeroRegisters) cpu entry
  memory := image
  devices := Devices.initial
  generation := 0
  power := true
  reservations := fun _ => none
  image := image
  log := []
  views := fun _ => 0

end Xv6.Kernel.MycpuBareWitness
