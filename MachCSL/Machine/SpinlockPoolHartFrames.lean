import MachCSL.Machine.SpinlockPoolOccurrenceProofs

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.SpinlockProtocol

/-- Structural facts derived from the unchanged hardware HartStep relation. -/
structure HartFrame (g g' : State) (cpu : CPU) : Prop where
  generation : g'.generation = g.generation
  power : g'.power = g.power
  image : g'.image = g.image
  registers : ∀ other, other ≠ cpu → g'.registers other = g.registers other
  reservations : ∀ other, other ≠ cpu → g'.reservations other = g.reservations other
  views : ∀ other, other ≠ cpu → g'.views other = g.views other
  log : ∃ tail, g'.log = g.log ++ tail

theorem hart_frame [Platform] {g g' : State} {cpu : CPU} {program program' : SailM Unit}
    (step : HartStep g cpu program program' g') : HartFrame g g' cpu := by
  obtain ⟨after, node, rfl⟩ := step
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro other different; simp [writeBack, updateHart, different]
  · intro other different; simp [writeBack, updateHart, different]
  · intro other different; simp [writeBack, updateHart, different]
  · rcases node_log_cases Devices.bus (othersReserved g.reservations cpu) (hartAgent cpu)
      g.image (focus g cpu) after program program' node with same | ⟨message, append⟩
    · exact ⟨[], by simpa [writeBack, focus] using same⟩
    · exact ⟨[message], append⟩

theorem live_hart_frame [Platform] {g g' : State} {gen : Nat} {cpu : CPU}
    {program program' : SailM Unit} {observations : List Observation} {forks : List Expr}
    (live : ThreadLive g gen)
    (step : Step SpinlockImage.image (.hart gen cpu program) g observations
      (.hart gen cpu program') g' forks) : HartFrame g g' cpu := by
  cases step with
  | hartDead _ _ _ _ dead => exact False.elim (dead live)
  | hartLive _ _ _ _ _ _ _ actual => exact hart_frame actual

theorem control_other {g g' : State} {cpu other : CPU} {program : SailM Unit} {c : Cursor}
    (frame : HartFrame g g' cpu) (different : other ≠ cpu)
    (control : CursorControl g other program c) : CursorControl g' other program c := by
  refine ⟨?_, ?_, control.2.2⟩
  · rw [OwnedMatch, frame.registers other different]
    exact control.1
  · rw [frame.reservations other different]
    exact control.2.1

theorem winning_other {g g' : State} {cpu other : CPU} {B : Nat}
    (frame : HartFrame g g' cpu) (different : other ≠ cpu)
    (winning : Winning g other B) : Winning g' other B := by
  refine ⟨winning.1, ?_, ?_⟩
  · rw [frame.views other different]
    exact winning.2.1
  · obtain ⟨tail, append⟩ := frame.log
    rw [append, List.getElem?_append_left (List.getElem?_eq_some_iff.mp winning.2.2).choose]
    exact winning.2.2

/-- An existing other holder keeps its owner, counter value and timestamp. -/
def OtherOwners (w w' : Words) (cpu : CPU) : Prop :=
  ∀ other B, other ≠ cpu → w.owner = some (other, B) →
    w'.owner = some (other, B) ∧ w'.counter = w.counter ∧ w'.counterTime = w.counterTime

/-- Any post-owner other than the selected CPU was already the owner. -/
def OtherOwnersBack (w w' : Words) (cpu : CPU) : Prop :=
  ∀ other B, other ≠ cpu → w'.owner = some (other, B) → w.owner = some (other, B)

theorem held_other {g g' : State} {w w' : Words} {cpu other : CPU} {B v t}
    (frame : HartFrame g g' cpu) (different : other ≠ cpu) (owners : OtherOwners w w' cpu)
    (held : HeldFacts g w other B v t) : HeldFacts g' w' other B v t := by
  obtain ⟨owner, value, time⟩ := owners other B different held.1
  exact ⟨owner, value.trans held.2.1, time.trans held.2.2.1, winning_other frame different held.2.2.2⟩

theorem phase_other {g g' : State} {w w' : Words} {cpu other : CPU} {c : Cursor}
    (frame : HartFrame g g' cpu) (different : other ≠ cpu) (owners : OtherOwners w w' cpu)
    (ok : PhaseOK g w other c) : PhaseOK g' w' other c := by
  cases phase : c.phase with
  | idle => simp only [PhaseOK, phase]
  | reserved old => simpa only [PhaseOK, phase] using ok
  | held B v t =>
    simp only [PhaseOK, phase] at ok ⊢
    exact ⟨held_other frame different owners ok.1, ok.2⟩
  | loaded B v t =>
    simp only [PhaseOK, phase] at ok ⊢
    exact ⟨held_other frame different owners ok.1, ok.2⟩
  | stored B v t =>
    simp only [PhaseOK, phase] at ok ⊢
    exact held_other frame different owners ok

end MachCSL.Machine.SpinlockPool
