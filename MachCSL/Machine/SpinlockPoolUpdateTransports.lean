import MachCSL.Machine.SpinlockPoolUpdateProofs

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan Logic.SpinlockProtocol

theorem read_transition [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (r : Register) (k : RegisterType r → SailM Unit)
    (control : CursorControl g cpu (.impure (.readReg r) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.readReg r) k)) g observations e' g' forks) :
    ∃ program', e' = .hart gen cpu program' ∧ forks = [] ∧
      Transition (.hart gen cpu (.impure (.readReg r) k), .hart c) g observations
        (.hart gen cpu program', .hart c) g' [] ∧ CursorControl g' cpu program' c := by
  obtain ⟨program', e, state, rfl, forks, edge, after⟩ := read_transport r k control live step
  exact ⟨program', e, forks, .hart live edge (update_read_register g g' cpu c r k), after⟩

theorem write_transition [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (r : Register) (value : RegisterType r) (k : Unit → SailM Unit)
    (control : CursorControl g cpu (.impure (.writeReg r value) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.writeReg r value) k)) g observations e' g' forks) :
    ∃ c', e' = .hart gen cpu (k ()) ∧ forks = [] ∧
      Transition (.hart gen cpu (.impure (.writeReg r value) k), .hart c) g observations
        (.hart gen cpu (k ()), .hart c') g' [] ∧ CursorControl g' cpu (k ()) c' := by
  obtain ⟨c', e, rfl, forks, edge, after⟩ := write_transport r value k control live step
  refine ⟨c', e, forks, .hart live edge ?_, after⟩
  cases edge with
  | writeOwned _ _ _ owned => simp [nextCursor, owned]

theorem restart_transition [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (control : CursorControl g cpu (.pure ()) c) (live : ThreadLive g gen)
    {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.pure ())) g observations e' g' forks) :
    ∃ tick c', e' = .hart gen cpu (cycle tick) ∧ forks = [] ∧
      Transition (.hart gen cpu (.pure ()), .hart c) g observations
        (.hart gen cpu (cycle tick), .hart c') g' [] ∧ CursorControl g' cpu (cycle tick) c' := by
  obtain ⟨tick, rfl, rfl, rfl, rfl⟩ :=
    RestartWP.restart_successors _ g gen cpu live observations e' g' forks step
  obtain ⟨i, family⟩ := EventPlanHead.pure_iff.mp control.2.2
  refine ⟨tick, { c with fetch := i, reservation := none }, rfl, rfl,
    .hart live (.restart c i tick family) (update_restart g cpu c i family.pc),
    control.1, ?_, SpinlockFamily.cycle_plan i family none tick⟩
  simp [RestartWP.clearReservation, updateHart]

/-- Both concrete exclusive-read successors inhabit the deterministic graph.
The returned word is obtained from actual current memory, not chosen by Plan. -/
theorem exclusive_transition [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (w : Words) (words : WordsOK g w) (memory : MemoryOK g)
    (k : MemoryReadWP.ReadResult 4 → SailM Unit)
    (control : CursorControl g cpu (.impure (.readMem 4 lockRead) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.readMem 4 lockRead) k))
      g observations e' g' forks) :
    ∃ program' c', e' = .hart gen cpu program' ∧ forks = [] ∧
      Transition (.hart gen cpu (.impure (.readMem 4 lockRead) k), .hart c) g observations
        (.hart gen cpu program', .hart c') g' [] ∧
      CursorControl g' cpu program' c' ∧ PhaseOK g' w cpu c' ∧ WordsOK g' w := by
  have head := EventPlanHead.head_of_plan control.2.2
  cases head with
  | codeRead ram plain allowed rest => contradiction
  | plain enabled ram kind rest => contradiction
  | exclusive enabled ram kind rest =>
    have idle : c.phase = .idle := enabled.1
    rcases MemoryExclusiveWP.step_inv _ g gen cpu 4 lockRead k ram kind live observations e' g' forks step with
      ⟨blocked, rfl, rfl, rfl, rfl⟩ | ⟨free, word, read, rfl, rfl, rfl, rfl⟩
    · refine ⟨_, { c with reservation := none }, rfl, rfl,
        .hart live (.exclusiveBlocked c 4 lockRead k enabled ram kind)
          (update_exclusive_blocked g cpu c k idle),
        ⟨control.1, ?_, blocked_exclusive_plan control.2.2 kind⟩, ?_, words⟩
      · simp [RestartWP.clearReservation, updateHart]
      · simp only [PhaseOK, idle]
    · have actual := latest_word_current memory words.1
      have same : word = w.lockValue := Option.some.inj (read.symm.trans actual)
      subst word
      have binary : w.lockValue = 0#32 ∨ w.lockValue = 1#32 := by
        unfold Words.lockValue
        split <;> simp
      have related : relations.exclusive c.phase 4 lockRead w.lockValue (.reserved w.lockValue) := by
        rw [idle]
        exact ExclusiveStep.reserve w.lockValue binary
      refine ⟨_, { c with phase := .reserved w.lockValue, reservation := some (snapshot lockRead.pa 4 w.lockValue) },
        rfl, rfl, .hart live (.exclusive c 4 lockRead w.lockValue (.reserved w.lockValue) k related ram kind)
          (update_exclusive_success g cpu c k idle w.lockValue binary actual),
        ⟨control.1, ?_, rest _ _ related⟩, ?_, words⟩
      · exact (MemoryExclusiveWP.acquired_reservation g cpu lockRead.pa 4 w.lockValue).symm
      · exact ⟨binary, rfl⟩

/-- Deterministic annotation of every actual reserved swap-write successor. -/
theorem reserved_swap_transition [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (w : Words) (words : WordsOK g w) (memory : MemoryOK g) (reservations : ReservationsOK g)
    (old : BitVec 32) (phase : c.phase = .reserved old) (ok : PhaseOK g w cpu c)
    (k : MemoryWriteWP.WriteResult → SailM Unit)
    (control : CursorControl g cpu (.impure (.writeMem 4 swapWrite) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.writeMem 4 swapWrite) k))
      g observations e' g' forks) :
    ∃ program' c' w', e' = .hart gen cpu program' ∧ forks = [] ∧
      Transition (.hart gen cpu (.impure (.writeMem 4 swapWrite) k), .hart c) g observations
        (.hart gen cpu program', .hart c') g' [] ∧
      CursorControl g' cpu program' c' ∧ PhaseOK g' w' cpu c' ∧ WordsOK g' w' ∧
      SwapEffect g cpu c w old g' c' w' := by
  obtain ⟨program', c', w', e, rfl, forks, edge, after, phaseAfter, wordsAfter, effect⟩ :=
    reserved_swap_transport w words memory reservations old phase ok k control live step
  exact ⟨program', c', w', e, forks, .hart live edge (update_swap_effect k phase words effect),
    after, phaseAfter, wordsAfter, effect⟩

end MachCSL.Machine.SpinlockPool
