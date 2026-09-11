import MachCSL.Machine.SpinlockPoolExclusive
import MachCSL.Logic.MemoryWriteWPState

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan Logic.SpinlockProtocol

def acquiredWords (w : Words) (cpu : CPU) (position : Nat) : Words :=
  { w with owner := some (cpu, position), lockTime := position }

def failedWords (w : Words) (position : Nat) : Words := { w with lockTime := position }

/-- The actual generated swap request advances the writer view to the new log
position; the preceding exclusive read alone would leave it one position short. -/
theorem swap_write_exclusive : accessExclusive swapWrite.access_kind = true := rfl

/-- Exact physical/cursor/history alternatives retained for subsequent pool framing. -/
inductive SwapEffect (g : State) (cpu : CPU) (c : Cursor) (w : Words) (old : BitVec 32) :
    State → Cursor → Words → Prop where
  | blocked : SwapEffect g cpu c w old g c w
  | won (zero : old = 0#32) (freeOwner : w.owner = none) :
      SwapEffect g cpu c w old (MemoryWriteWP.writeState g cpu swapWrite 1#32)
        { c with phase := .held (g.log.length + 1) w.counter w.counterTime, reservation := none }
        (acquiredWords w cpu (g.log.length + 1))
  | lost (one : old = 1#32) :
      SwapEffect g cpu c w old (MemoryWriteWP.writeState g cpu swapWrite 1#32)
        { c with phase := .idle, reservation := none } (failedWords w (g.log.length + 1))

theorem lock_zero_owner (w : Words) (zero : w.lockValue = 0#32) : w.owner = none := by
  cases owner : w.owner with
  | none => rfl
  | some pair =>
    simp [Words.lockValue, owner] at zero

private theorem counter_frame {g w} (words : WordsOK g w) (cpu : CPU) :
    LatestWord (MemoryWriteWP.writeState g cpu swapWrite 1#32)
      SpinlockImage.counterAddress w.counter w.counterTime :=
  latest_word_frame words.2 SpinlockImage.lockAddress 1#32 (hartAgent cpu)
    (fun address counter lock => SpinlockImage.data_separate address lock counter)

private theorem winning_append (g : State) (cpu : CPU) :
    Winning (MemoryWriteWP.writeState g cpu swapWrite 1#32) cpu (g.log.length + 1) := by
  refine ⟨by omega, ?_, ?_⟩
  · rw [MemoryWriteWP.writeState_view]
    exact Nat.le_refl _
  · simp only [MemoryWriteWP.writeState, Nat.add_sub_cancel, List.getElem?_append_right (Nat.le_refl _),
      Nat.sub_self, List.getElem?_cons_zero]
    rfl

theorem reserved_current {g w cpu c old program}
    (words : WordsOK g w) (memory : MemoryOK g) (reservations : ReservationsOK g)
    (control : CursorControl g cpu program c) (phase : c.phase = .reserved old)
    (ok : PhaseOK g w cpu c) : old = w.lockValue := by
  have held : g.reservations cpu = some (snapshot SpinlockImage.lockAddress 4 old) := by
    rw [PhaseOK, phase] at ok
    exact control.2.1.symm.trans ok.2
  have oldRead := MemoryExclusiveWP.snapshot_read g.memory SpinlockImage.lockAddress 4 old
    (by decide) (reservations cpu _ held)
  exact Option.some.inj (oldRead.symm.trans (latest_word_current memory words.1))

/-- The actual reserved AMOSWAP write, including its blocked arm and both old
values. This is one event after the separately proved exclusive read; no whole
AMO atomicity or selected scheduler is assumed. -/
theorem reserved_swap_transport [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (w : Words) (words : WordsOK g w) (memory : MemoryOK g) (reservations : ReservationsOK g)
    (old : BitVec 32) (phase : c.phase = .reserved old) (ok : PhaseOK g w cpu c)
    (k : MemoryWriteWP.WriteResult → SailM Unit)
    (control : CursorControl g cpu (.impure (.writeMem 4 swapWrite) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.writeMem 4 swapWrite) k))
      g observations e' g' forks) :
    ∃ program' c' w', e' = .hart gen cpu program' ∧ observations = [] ∧ forks = [] ∧
      CursorEdge cpu c (.impure (.writeMem 4 swapWrite) k) c' program' ∧
      CursorControl g' cpu program' c' ∧ PhaseOK g' w' cpu c' ∧ WordsOK g' w' ∧
      SwapEffect g cpu c w old g' c' w' := by
  obtain ⟨value, enabled, present, ram, mode, eligible, rest⟩ := EventPlanHead.write_memory_cases control.2.2
  have val : value = 1#32 := Option.some.inj present.symm
  subst value
  rcases MemoryWriteWP.step_inv _ g gen cpu 4 swapWrite 1#32 k rfl ram live observations e' g' forks step with
    ⟨blocked, rfl, rfl, rfl, rfl⟩ | ⟨free, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, c, w, rfl, rfl, rfl, .writeBlocked c 4 swapWrite 1#32 k rfl ram mode eligible,
      control, ok, words, .blocked⟩
  · have current := reserved_current words memory reservations control phase ok
    have binary : old = 0#32 ∨ old = 1#32 := by rw [PhaseOK, phase] at ok; exact ok.1
    rcases binary with rfl | rfl
    · let B := g.log.length + 1
      let next := Phase.held B w.counter w.counterTime
      have bound : w.counterTime ≤ B := Nat.le_trans (latest_word_bound words.2) (Nat.le_succ _)
      have related : relations.write c.phase 4 swapWrite 1#32 next := by
        rw [phase]
        exact WriteStep.acquire B w.counter w.counterTime bound
      refine ⟨_, { c with phase := next, reservation := none }, acquiredWords w cpu B,
        rfl, rfl, rfl, .write c 4 swapWrite 1#32 next k rfl ram mode eligible related,
        ⟨control.1, ?_, rest _ related⟩, ?_, ?_, .won rfl (lock_zero_owner w current.symm)⟩
      · simp [MemoryWriteWP.writeState, updateHart]
      · exact ⟨⟨rfl, rfl, rfl, winning_append g cpu⟩, bound⟩
      · exact ⟨latest_word_append g SpinlockImage.lockAddress 1#32 (hartAgent cpu), counter_frame words cpu⟩
    · have related : relations.write c.phase 4 swapWrite 1#32 .idle := by
        rw [phase]
        exact WriteStep.failed
      refine ⟨_, { c with phase := .idle, reservation := none }, failedWords w (g.log.length + 1),
        rfl, rfl, rfl, .write c 4 swapWrite 1#32 .idle k rfl ram mode eligible related,
        ⟨control.1, ?_, rest _ related⟩, True.intro, ?_, .lost rfl⟩
      · simp [MemoryWriteWP.writeState, updateHart]
      · refine ⟨?_, counter_frame words cpu⟩
        change LatestWord _ SpinlockImage.lockAddress w.lockValue (g.log.length + 1)
        rw [← current]
        exact latest_word_append g SpinlockImage.lockAddress 1#32 (hartAgent cpu)

end MachCSL.Machine.SpinlockPool
