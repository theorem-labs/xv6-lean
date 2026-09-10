import MachCSL.Sail.Execution

/-! Total dependent register files and their event handler. The concrete
register-type encoding and its correspondence to Rocq's register record remain
separate. This handler covers register events only; it is not the machine. -/
namespace MachCSL.Sail.Registers

variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register]

abbrev File (RegisterType : Register → Type) := (reg : Register) → RegisterType reg

def write (registers : File RegisterType) (reg : Register) (value : RegisterType reg) :
    File RegisterType := fun other =>
  if h : reg = other then h ▸ value else registers other

@[simp] theorem write_same (registers : File RegisterType) (reg : Register)
    (value : RegisterType reg) : write registers reg value reg = value := by
  simp [write]

theorem write_other (registers : File RegisterType) (reg other : Register)
    (value : RegisterType reg) (h : reg ≠ other) :
    write registers reg value other = registers other := by
  simp [write, h]

theorem write_overwrite (registers : File RegisterType) (reg : Register)
    (first second : RegisterType reg) :
    write (write registers reg first) reg second = write registers reg second := by
  funext other
  by_cases h : reg = other
  · subst other
    simp
  · simp [write, h]

theorem write_current (registers : File RegisterType) (reg : Register) :
    write registers reg (registers reg) = registers := by
  funext other
  by_cases h : reg = other
  · subst other
    simp
  · simp [write, h]

theorem write_comm (registers : File RegisterType) (left right : Register)
    (leftValue : RegisterType left) (rightValue : RegisterType right) (h : left ≠ right) :
    write (write registers left leftValue) right rightValue =
      write (write registers right rightValue) left leftValue := by
  funext other
  by_cases hl : left = other
  · subst other
    simp [write, Ne.symm h]
  · by_cases hr : right = other
    · subst other
      simp [write, h]
    · simp [write, hl, hr]

open _root_.Sail.ConcurrencyInterfaceV1.Free
variable [_root_.Sail.ConcurrencyInterfaceV1.Arch] {ue : Type}

/-- Exactly the register-read and register-write rules on this total file. -/
def handler : Execution.Handler RegisterType ue (File RegisterType) :=
  fun event before result after => match event with
    | .readReg reg => result = before reg ∧ after = before
    | .writeReg reg value => after = write before reg value
    | _ => False

theorem read_step (registers : File RegisterType) (reg : Register)
    (continuation : RegisterType reg → PreSailM RegisterType ue α) :
    Execution.Step handler (.impure (.readReg reg) continuation, registers)
      ⟨.readReg reg, registers reg⟩ (continuation (registers reg), registers) :=
  .event ⟨rfl, rfl⟩

theorem write_step (registers : File RegisterType) (reg : Register) (value : RegisterType reg)
    (continuation : Unit → PreSailM RegisterType ue α) :
    Execution.Step handler (.impure (.writeReg reg value) continuation, registers)
      ⟨.writeReg reg value, ()⟩ (continuation (), write registers reg value) :=
  .event rfl

end MachCSL.Sail.Registers
