import MachCSL.Machine.SpinlockPoolMemoryTransports

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan Logic.SpinlockProtocol

def incrementedWords (w : Words) (value : BitVec 32) (time : Nat) : Words :=
  { w with counter := value, counterTime := time }

def releasedWords (w : Words) (time : Nat) : Words := { w with owner := none, lockTime := time }

inductive CounterEffect (g : State) (cpu : CPU) (c : Cursor) (w : Words)
    (B : Nat) (v : BitVec 32) (t : Nat) : State → Cursor → Words → Prop where
  | blocked : CounterEffect g cpu c w B v t g c w
  | committed (owner : w.owner = some (cpu, B)) :
      CounterEffect g cpu c w B v t (MemoryWriteWP.writeState g cpu (counterWrite (v + 1#32)) (v + 1#32))
        { c with phase := .stored B (v + 1#32) (g.log.length + 1), reservation := none }
        (incrementedWords w (v + 1#32) (g.log.length + 1))

inductive UnlockEffect (g : State) (cpu : CPU) (c : Cursor) (w : Words)
    (B : Nat) : State → Cursor → Words → Prop where
  | blocked : UnlockEffect g cpu c w B g c w
  | committed (owner : w.owner = some (cpu, B)) :
      UnlockEffect g cpu c w B (MemoryWriteWP.writeState g cpu unlockWrite 0#32)
        { c with phase := .idle, reservation := none } (releasedWords w (g.log.length + 1))

/-- An ordinary append retains this CPU's view and its earlier winning
message. The receipt bound comes from the actual pre-log lookup. -/
theorem winning_ordinary_append {g : State} {cpu : CPU} {B : Nat}
    (winning : Winning g cpu B) (req : WriteRequest n) (value : BitVec (8 * n))
    (plain : accessExclusive req.access_kind = false) :
    Winning (MemoryWriteWP.writeState g cpu req value) cpu B := by
  refine ⟨winning.1, ?_, ?_⟩
  · simpa [MemoryWriteWP.writeState, MemoryWriteWP.postView, plain, updateHart] using winning.2.1
  · have bound := (List.getElem?_eq_some_iff.mp winning.2.2).choose
    change (g.log ++ [_])[B - 1]? = _
    rw [List.getElem?_append_left bound]
    exact winning.2.2

/-- The real counter store, including blocked writes, modular 32-bit
increment, actual new timestamp, and preservation of the original winner. -/
theorem counter_store_transition [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (w : Words) (words : WordsOK g w) (ok : PhaseOK g w cpu c)
    (B : Nat) (v : BitVec 32) (t : Nat) (phase : c.phase = .loaded B v t)
    (k : MemoryWriteWP.WriteResult → SailM Unit)
    (control : CursorControl g cpu (.impure (.writeMem 4 (counterWrite (v + 1#32))) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.writeMem 4 (counterWrite (v + 1#32))) k))
      g observations e' g' forks) :
    ∃ program' c' w', e' = .hart gen cpu program' ∧ forks = [] ∧
      Transition (.hart gen cpu (.impure (.writeMem 4 (counterWrite (v + 1#32))) k), .hart c) g observations
        (.hart gen cpu program', .hart c') g' [] ∧
      CursorControl g' cpu program' c' ∧ PhaseOK g' w' cpu c' ∧ WordsOK g' w' ∧
      CounterEffect g cpu c w B v t g' c' w' := by
  have held : HeldFacts g w cpu B v t ∧ t ≤ B := by simpa only [PhaseOK, phase] using ok
  obtain ⟨value, enabled, present, ram, mode, eligible, rest⟩ := EventPlanHead.write_memory_cases control.2.2
  have val : value = v + 1#32 := Option.some.inj present.symm
  subst value
  rcases MemoryWriteWP.step_inv _ g gen cpu 4 (counterWrite (v + 1#32)) (v + 1#32) k rfl ram live
      observations e' g' forks step with
    ⟨blocked, rfl, rfl, rfl, rfl⟩ | ⟨free, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, c, w, rfl, rfl,
      .hart live (.writeBlocked c 4 _ _ k rfl ram mode eligible)
        (by simp [nextCursor, expectedWrite, phase]), control, ok, words, .blocked⟩
  · have related : relations.write c.phase 4 (counterWrite (v + 1#32)) (v + 1#32)
        (.stored B (v + 1#32) (g.log.length + 1)) := by
      rw [phase]; exact WriteStep.increment B v t (g.log.length + 1)
    refine ⟨_, { c with phase := .stored B (v + 1#32) (g.log.length + 1), reservation := none },
      incrementedWords w (v + 1#32) (g.log.length + 1), rfl, rfl,
      .hart live (.write c 4 _ _ _ k rfl ram mode eligible related) ?_,
      ⟨control.1, ?_, rest _ related⟩, ?_, ?_, .committed held.1.1⟩
    · simp [nextCursor, expectedWrite, phase, MemoryWriteWP.writeState, committedPhase]
    · simp [MemoryWriteWP.writeState, updateHart]
    · exact ⟨held.1.1, rfl, rfl, winning_ordinary_append held.1.2.2.2 _ _ rfl⟩
    · exact ⟨latest_word_frame words.1 SpinlockImage.counterAddress (v + 1#32) (hartAgent cpu)
        SpinlockImage.data_separate,
        latest_word_append g SpinlockImage.counterAddress (v + 1#32) (hartAgent cpu)⟩

/-- The holder window closes at the actual successful zero-store event.
A blocked unlock keeps the stored phase and reservation unchanged. -/
theorem unlock_transition [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (w : Words) (words : WordsOK g w) (ok : PhaseOK g w cpu c)
    (B : Nat) (v : BitVec 32) (t : Nat) (phase : c.phase = .stored B v t)
    (k : MemoryWriteWP.WriteResult → SailM Unit)
    (control : CursorControl g cpu (.impure (.writeMem 4 unlockWrite) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.writeMem 4 unlockWrite) k))
      g observations e' g' forks) :
    ∃ program' c' w', e' = .hart gen cpu program' ∧ forks = [] ∧
      Transition (.hart gen cpu (.impure (.writeMem 4 unlockWrite) k), .hart c) g observations
        (.hart gen cpu program', .hart c') g' [] ∧
      CursorControl g' cpu program' c' ∧ PhaseOK g' w' cpu c' ∧ WordsOK g' w' ∧
      UnlockEffect g cpu c w B g' c' w' := by
  have held : HeldFacts g w cpu B v t := by simpa only [PhaseOK, phase] using ok
  obtain ⟨value, enabled, present, ram, mode, eligible, rest⟩ := EventPlanHead.write_memory_cases control.2.2
  have val : value = 0#32 := Option.some.inj present.symm
  subst value
  rcases MemoryWriteWP.step_inv _ g gen cpu 4 unlockWrite 0#32 k rfl ram live
      observations e' g' forks step with
    ⟨blocked, rfl, rfl, rfl, rfl⟩ | ⟨free, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, c, w, rfl, rfl,
      .hart live (.writeBlocked c 4 _ _ k rfl ram mode eligible)
        (by simp [nextCursor, expectedWrite, phase]), control, ok, words, .blocked⟩
  · have related : relations.write c.phase 4 unlockWrite 0#32 .idle := by
      rw [phase]; exact WriteStep.release B v t
    refine ⟨_, { c with phase := .idle, reservation := none }, releasedWords w (g.log.length + 1),
      rfl, rfl, .hart live (.write c 4 _ _ _ k rfl ram mode eligible related) ?_,
      ⟨control.1, ?_, rest _ related⟩, True.intro, ?_, .committed held.1⟩
    · simp [nextCursor, expectedWrite, phase, MemoryWriteWP.writeState, committedPhase]
    · simp [MemoryWriteWP.writeState, updateHart]
    · exact ⟨latest_word_append g SpinlockImage.lockAddress 0#32 (hartAgent cpu),
        latest_word_frame words.2 SpinlockImage.lockAddress 0#32 (hartAgent cpu)
          (fun address counter lock => SpinlockImage.data_separate address lock counter)⟩

end MachCSL.Machine.SpinlockPool
