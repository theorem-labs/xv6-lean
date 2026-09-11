import MachCSL.Machine.SpinlockPoolRegisters
import MachCSL.Machine.SpinlockPoolWords

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan Logic.SpinlockProtocol

private theorem lock_binary (w : Words) : w.lockValue = 0#32 ∨ w.lockValue = 1#32 := by
  unfold Words.lockValue
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- All actual successors of the concrete exclusive-read boundary. A blocked
read keeps the residual and clears rr; success records the real binary word
and exact snapshot without transferring the holder window. -/
theorem exclusive_transport [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (w : Words) (words : WordsOK g w) (memory : MemoryOK g)
    (k : MemoryReadWP.ReadResult 4 → SailM Unit)
    (control : CursorControl g cpu (.impure (.readMem 4 lockRead) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.readMem 4 lockRead) k))
      g observations e' g' forks) :
    ∃ program' c', e' = .hart gen cpu program' ∧ observations = [] ∧ forks = [] ∧
      CursorEdge cpu c (.impure (.readMem 4 lockRead) k) c' program' ∧
      CursorControl g' cpu program' c' ∧ PhaseOK g' w cpu c' ∧ WordsOK g' w := by
  have head := EventPlanHead.head_of_plan control.2.2
  cases head with
  | codeRead ram plain allowed rest => contradiction
  | plain enabled ram kind rest => contradiction
  | exclusive enabled ram kind rest =>
    have idle : c.phase = .idle := enabled.1
    rcases MemoryExclusiveWP.step_inv _ g gen cpu 4 lockRead k ram kind live observations e' g' forks step with
      ⟨blocked, rfl, rfl, rfl, rfl⟩ | ⟨free, word, read, rfl, rfl, rfl, rfl⟩
    · refine ⟨_, { c with reservation := none }, rfl, rfl, rfl,
        .exclusiveBlocked c 4 lockRead k enabled ram kind,
        ⟨control.1, ?_, blocked_exclusive_plan control.2.2 kind⟩, ?_, words⟩
      · simp [RestartWP.clearReservation, updateHart]
      · simp only [PhaseOK, idle]
    · have actual := latest_word_current memory words.1
      have same : word = w.lockValue := Option.some.inj (read.symm.trans actual)
      subst word
      have related : relations.exclusive c.phase 4 lockRead w.lockValue (.reserved w.lockValue) := by
        rw [idle]
        exact ExclusiveStep.reserve w.lockValue (lock_binary w)
      refine ⟨_, { c with phase := .reserved w.lockValue, reservation := some (snapshot lockRead.pa 4 w.lockValue) },
        rfl, rfl, rfl, .exclusive c 4 lockRead w.lockValue (.reserved w.lockValue) k related ram kind,
        ⟨control.1, ?_, rest _ _ related⟩, ?_, words⟩
      · exact (MemoryExclusiveWP.acquired_reservation g cpu lockRead.pa 4 w.lockValue).symm
      · exact ⟨lock_binary w, rfl⟩

end MachCSL.Machine.SpinlockPool
