import MachCSL.Machine.SpinlockPoolDefs

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan Logic.SpinlockProtocol

/-- Partial logical selection. Its uses below have separately proved uniqueness;
missing data produces none, never a default word, timestamp or instruction. -/
noncomputable def select {α : Type} (predicate : α → Prop) : Option α := by
  classical
  exact if found : ∃ value, predicate value then some found.choose else none

noncomputable def latestPair (g : State) (address : PhysicalAddress) : Option (BitVec 32 × Nat) :=
  select fun pair => LatestWord g address pair.1 pair.2

noncomputable def boundaryIndex (rs : RegisterFile) : Option (Fin 17) :=
  select fun i => rs .PC = SpinlockImage.instructionAddress i

/-- The actual successful data-write phase update. All new timestamps come
from the pre-state log; only acquisition consults the canonical counter pair. -/
noncomputable def committedPhase (g : State) : Phase → Option Phase
  | .reserved old => if old = 0#32 then
      (latestPair g SpinlockImage.counterAddress).map fun pair =>
        .held (g.log.length + 1) pair.1 pair.2
    else if old = 1#32 then some .idle else none
  | .loaded B value _ => some (.stored B (value + 1#32) (g.log.length + 1))
  | .stored _ _ _ => some .idle
  | _ => none

def expectedWrite : Phase → Option ((n : Nat) × WriteRequest n)
  | .reserved _ => some ⟨4, swapWrite⟩
  | .loaded _ value _ => some ⟨4, counterWrite (value + 1#32)⟩
  | .stored _ _ _ => some ⟨4, unlockWrite⟩
  | _ => none

/-- A deterministic annotation update for a fixed actual pre/post machine
step. CursorEdge separately certifies the event result and continuation.
This function neither assumes nor asserts preservation of PoolInv. -/
noncomputable def nextCursor (g g' : State) (cpu : CPU) (program : SailM Unit)
    (c : Cursor) : Option Cursor := by
  classical
  exact match program with
  | .pure () => (boundaryIndex c.registers).map fun i =>
      { c with fetch := i, reservation := none }
  | .impure event _ => match event with
    | .readReg _ => some c
    | .writeReg r value => if EventWP.IsOwned r then
        some { c with registers := Sail.Registers.write c.registers r value } else none
    | .readMem n req =>
        if accessExclusive req.access_kind then
          if c.phase = .idle ∧ (⟨n, req⟩ : (n : Nat) × ReadRequest n) = ⟨4, lockRead⟩ then
            if g'.reservations cpu = none then some { c with reservation := none }
            else (readBytes g.memory SpinlockImage.lockAddress 4).bind fun old =>
              if old = 0#32 ∨ old = 1#32 then
                some { c with phase := .reserved old, reservation := some (snapshot SpinlockImage.lockAddress 4 old) }
              else none
          else none
        else if ∃ word, SpinlockFetch.CodeRead c.fetch n req word then some c
        else if (⟨n, req⟩ : (n : Nat) × ReadRequest n) = ⟨4, counterRead⟩ then
          match c.phase with
          | .held B value time => some { c with phase := .loaded B value time }
          | _ => none
        else none
    | .writeMem n req =>
        if expectedWrite c.phase = some ⟨n, req⟩ then
          if g'.log.length = g.log.length then some c
          else if g'.log.length = g.log.length + 1 then
            (committedPhase g c.phase).map fun phase =>
              { c with phase := phase, reservation := none }
          else none
        else none
    | .barrier kind =>
        if kind = .Barrier_RISCV_rw_w then match c.phase with
          | .stored _ _ _ => some c
          | _ => none
        else none
    | _ => none

end MachCSL.Machine.SpinlockPool
