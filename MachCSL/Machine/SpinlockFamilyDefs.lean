import MachCSL.Machine.SpinlockCoreProofs
import MachCSL.Logic.SpinlockProtocolDefs

namespace MachCSL.Machine.SpinlockFamily
open Logic.SpinlockProtocol LeanPaperStock.Functions

/-- The protocol and operand facts at each of the seventeen instruction boundaries.
No operand constraint is imposed before the initial CSR read. -/
def At (cpu : CPU) (i : Fin 17) (rs : RegisterFile) (phase : Phase) : Prop :=
  match i.val with
  | 0 => phase = .idle
  | 1 => phase = .idle ∧ rs .x5 = BitVec.ofNat 64 cpu.val
  | 2 => phase = .idle ∧ rs .x6 = if cpu.val < 2 then 1#64 else 0#64
  | 3 => phase = .idle
  | 4 => phase = .idle ∧ rs .x10 = SpinlockImage.lockAddress + 12#64
  | 5 | 6 => phase = .idle
  | 7 => phase = .idle ∧ rs .x15 = 1#64
  | 8 | 9 => (phase = .idle ∧ rs .x15 = 1#64) ∨
      ∃ B v t, phase = .held B v t ∧ rs .x15 = 0#64
  | 10 => ∃ B v t, phase = .held B v t
  | 11 => ∃ B v t, phase = .loaded B v t ∧ rs .x16 = sign_extend (m := 64) v
  | 12 => ∃ B v t, phase = .loaded B v t ∧ rs .x16 = sign_extend (m := 64) (v + 1#32)
  | 13 | 14 => ∃ B v t, phase = .stored B v t
  | 15 => phase = .idle
  | _ => phase = .idle ∧ 2 ≤ cpu.val

structure Operands (cpu : CPU) (i : Fin 17) (rs : RegisterFile) (phase : Phase) : Prop where
  participant : 3 ≤ i.val → i.val ≤ 15 → cpu.val < 2
  base : 5 ≤ i.val → i.val ≤ 15 → rs .x10 = SpinlockImage.lockAddress
  one : 6 ≤ i.val → i.val ≤ 15 → rs .x14 = 1#64
  stage : At cpu i rs phase

structure Family (cpu : CPU) (i : Fin 17) (rs : RegisterFile) (phase : Phase) : Prop where
  core : SpinlockCore.Core cpu rs
  operands : Operands cpu i rs phase
  pc : rs .PC = SpinlockImage.instructionAddress i
  nextPC : rs .nextPC = SpinlockImage.instructionAddress i

/-- Input to execute after the real enable/default-nextPC prefix. -/
structure Ready (cpu : CPU) (i : Fin 17) (rs : RegisterFile) (phase : Phase) : Prop where
  core : SpinlockCore.Core cpu rs
  operands : Operands cpu i rs phase
  pc : rs .PC = SpinlockImage.instructionAddress i
  nextPC : rs .nextPC = Sail.BitVec.addInt (rs .PC) 4

/-- The instruction chooses an in-image successor; cycle subsequently commits PC. -/
structure Completed (cpu : CPU) (rs : RegisterFile) (phase : Phase) : Prop where
  core : SpinlockCore.Core cpu rs
  next : ∃ i : Fin 17, Operands cpu i rs phase ∧ rs .nextPC = SpinlockImage.instructionAddress i

end MachCSL.Machine.SpinlockFamily
