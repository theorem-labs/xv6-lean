import MachCSL.Sail.Interface

/-!
A result-carrier slice of the Rocq V1 correspondence, transcribed from
coq-sail 0.20.1 (927111b2f61fe6208a7c24539167a7bec5d9d21d).

`Sum` transcribes Rocq's `+`; `Unit`, `Bool`, `Int`, `String` and `BitVec`
stand for the corresponding source carriers after a still-unproved base-type
translation. These are Lean proofs about that transcription, not checked
translation of Rocq definitions, request correspondence, or machine refinement.
See docs/Sail-correspondence.md for the source and remaining obligations.
-/
namespace MachCSL.Sail.Correspondence

open _root_.Sail.ConcurrencyInterfaceV1
open _root_.Sail.ConcurrencyInterfaceV1.Free

/-- A total, invertible result transport; it neither drops nor adds results. -/
structure ResultCode (Source Target : Type) where
  encode : Source → Target
  decode : Target → Source
  decode_encode : ∀ value, decode (encode value) = value
  encode_decode : ∀ value, encode (decode value) = value

def identityCode (α : Type) : ResultCode α α where
  encode := id
  decode := id
  decode_encode _ := rfl
  encode_decode _ := rfl

/-- Rocq V1 uses `success + abort`, whereas Lean Sail uses `Result`. -/
def sumCode (α Abort : Type) : ResultCode (Sum α Abort) (_root_.Sail.Result α Abort) where
  encode
    | .inl value => .Ok value
    | .inr error => .Err error
  decode
    | .Ok value => .inl value
    | .Err error => .inr error
  decode_encode value := by cases value <;> rfl
  encode_decode value := by cases value <;> rfl

variable {Register : Type} {RegisterType : Register → Type} [Arch] {ue : Type}

/-- Only the result carrier is mapped; register and architecture translation
is not established by this definition. -/
def registerReadCode (reg : Register) :
    ResultCode (RegisterType reg) (Event.Result RegisterType (.readReg (ue := ue) reg)) :=
  identityCode _

def registerWriteCode (reg : Register) (value : RegisterType reg) :
    ResultCode Unit (Event.Result RegisterType (.writeReg (ue := ue) reg value)) :=
  identityCode _

def barrierCode (barrier : Arch.barrier) :
    ResultCode Unit (Event.Result RegisterType (.barrier (ue := ue) barrier)) :=
  identityCode _

def messageCode (message : String) :
    ResultCode Unit (Event.Result RegisterType (.print (ue := ue) message)) :=
  identityCode _

def readCode (request : Mem_read_request n Arch.va_size Arch.pa Arch.translation Arch.arch_ak) :
    ResultCode (Sum (BitVec (8 * n) × Option Bool) Arch.abort)
      (Event.Result RegisterType (.readMem (ue := ue) n request)) :=
  sumCode _ _

/-- This transports write responses, including aborts. It does not resolve the
Rocq mandatory write payload versus Lean optional write payload mismatch. -/
def writeCode (request : Mem_write_request n Arch.va_size Arch.pa Arch.translation Arch.arch_ak) :
    ResultCode (Sum (Option Bool) Arch.abort)
      (Event.Result RegisterType (.writeMem (ue := ue) n request)) :=
  sumCode _ _

def boolChoiceCode : ResultCode Bool
    (Event.Result RegisterType (.choose (ue := ue) .bool)) := identityCode _

def intChoiceCode : ResultCode Int
    (Event.Result RegisterType (.choose (ue := ue) .int)) := identityCode _

def stringChoiceCode : ResultCode String
    (Event.Result RegisterType (.choose (ue := ue) .string)) := identityCode _

/-- Requires the outstanding correspondence of Rocq `mword` at this width with
Lean `BitVec`; negative Rocq widths are outside this common-carrier slice. -/
def bitvectorChoiceCode (n : Nat) : ResultCode (BitVec n)
    (Event.Result RegisterType (.choose (ue := ue) (.bitvector n))) := identityCode _

omit [Arch] in
/-- Moving a result predicate across a code preserves every possible result. -/
theorem exists_encoded_iff (code : ResultCode Source Target) (P : Target → Prop) :
    (∃ source, P (code.encode source)) ↔ ∃ target, P target := by
  constructor
  · rintro ⟨source, h⟩
    exact ⟨code.encode source, h⟩
  · rintro ⟨target, h⟩
    exact ⟨code.decode target, by simpa only [code.encode_decode] using h⟩

omit [Arch] in
/-- Continuations agree for all source responses iff they agree after decoding
all target responses. This is a result-level premise, not a tree simulation. -/
theorem continuation_iff (code : ResultCode Source Target)
    (source : Source → α) (target : Target → α) :
    (∀ value, source value = target (code.encode value)) ↔
      ∀ value, source (code.decode value) = target value := by
  constructor
  · intro h value
    simpa only [code.encode_decode] using h (code.decode value)
  · intro h value
    simpa only [code.decode_encode] using h (code.encode value)

/-- The paper returns this success response in every completed memory read. -/
theorem read_success (w : BitVec (8 * n)) :
    (sumCode (BitVec (8 * n) × Option Bool) Arch.abort).encode (.inl (w, none)) =
      .Ok (w, none) := rfl

/-- The paper returns this success response in every completed memory write. -/
theorem write_success :
    (sumCode (Option Bool) Arch.abort).encode (.inl none) = .Ok none := rfl

end MachCSL.Sail.Correspondence
