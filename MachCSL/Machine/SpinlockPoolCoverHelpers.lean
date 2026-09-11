import MachCSL.Machine.SpinlockPoolOwnerProofs
import MachCSL.Machine.SpinlockPoolWorkerCoverProofs

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan Logic.SpinlockProtocol

theorem transition_hart_observations [Platform] {gen : Nat} {cpu : CPU} {program : SailM Unit}
    {c c' : Cursor} {g g' : State} {observations : List Observation} {e' : Expr} {forks : Pool}
    (transition : Transition (.hart gen cpu program, .hart c) g observations (e', .hart c') g' forks) :
    observations = [] := by cases transition <;> rfl

theorem transition_nonwrite_holder [Platform] {gen : Nat} {cpu : CPU} {program : SailM Unit}
    {c c' : Cursor} {g g' : State} {observations : List Observation} {e' : Expr} {forks : Pool}
    (transition : Transition (.hart gen cpu program, .hart c) g observations (e', .hart c') g' forks)
    (nonwrite : writeEvent program = false) : HolderPosition c'.phase = HolderPosition c.phase := by
  cases transition with
  | hart live edge update => exact edge_nonwrite_holder edge nonwrite
  | stale dead => rfl

theorem covered_of_selected [Platform] {left right : Pool} {g g' : State} {gen : Nat} {cpu : CPU}
    {program program' : SailM Unit} {c c' : Cursor} {w w' : Words}
    {observations : List Observation} {e' : Expr} {forks : List Expr}
    (inv : PoolInv (left ++ (.hart gen cpu program, .hart c) :: right, g))
    (live : ThreadLive g gen) (oldControl : CursorControl g cpu program c)
    (oldCursors : LiveCursors (left ++ (.hart gen cpu program, .hart c) :: right) g w)
    (oldOwner : OwnerPresent (left ++ (.hart gen cpu program, .hart c) :: right) g w)
    (step : Step SpinlockImage.image (.hart gen cpu program) g observations e' g' forks)
    (target : e' = .hart gen cpu program') (noForks : forks = [])
    (transition : Transition (.hart gen cpu program, .hart c) g observations
      (.hart gen cpu program', .hart c') g' [])
    (control : CursorControl g' cpu program' c') (phase : PhaseOK g' w' cpu c')
    (words : WordsOK g' w') (owners : OwnerFacts w w' cpu c') :
    Covered left right (.hart gen cpu program) (.hart c) g observations e' g' forks := by
  subst e'
  subst forks
  have noObs := transition_hart_observations transition
  subst observations
  have code := (inv.2 live.1).2.2.2.2.1
  obtain ⟨devices, codeAfter⟩ := step_scenery oldControl code live step
  refine ⟨.hart c', [], rfl, transition, ?_⟩
  simpa only [List.append_nil] using pool_replace_hart inv live oldCursors oldOwner step control phase words
    devices codeAfter owners.1 owners.2.1 owners.2.2

theorem covered_of_nonwrite [Platform] {left right : Pool} {g g' : State} {gen : Nat} {cpu : CPU}
    {program program' : SailM Unit} {c c' : Cursor} {w : Words}
    {observations : List Observation} {e' : Expr} {forks : List Expr}
    (inv : PoolInv (left ++ (.hart gen cpu program, .hart c) :: right, g))
    (live : ThreadLive g gen) (oldControl : CursorControl g cpu program c)
    (oldCursors : LiveCursors (left ++ (.hart gen cpu program, .hart c) :: right) g w)
    (oldOwner : OwnerPresent (left ++ (.hart gen cpu program, .hart c) :: right) g w)
    (step : Step SpinlockImage.image (.hart gen cpu program) g observations e' g' forks)
    (target : e' = .hart gen cpu program') (noForks : forks = [])
    (transition : Transition (.hart gen cpu program, .hart c) g observations
      (.hart gen cpu program', .hart c') g' [])
    (control : CursorControl g' cpu program' c') (phase : PhaseOK g' w cpu c')
    (words : WordsOK g' w) (nonwrite : writeEvent program = false) :
    Covered left right (.hart gen cpu program) (.hart c) g observations e' g' forks := by
  apply covered_of_selected inv live oldControl oldCursors oldOwner step target noForks transition control phase words
  exact owner_same (fun B owner => selected_owner_phase inv.1 live oldOwner owner)
    (transition_nonwrite_holder transition nonwrite)

theorem family_not_reserved {cpu : CPU} {i : Fin 17} {rs : RegisterFile} {phase : Phase}
    (family : SpinlockFamily.Family cpu i rs phase) (word : BitVec 32) : phase ≠ .reserved word := by
  intro equal
  have stage := family.operands.stage
  unfold SpinlockFamily.At at stage
  split at stage <;> simp_all

theorem restart_phase {g : State} {cpu : CPU} {c : Cursor} {w : Words} {i : Fin 17}
    (family : SpinlockFamily.Family cpu i c.registers c.phase) (ok : PhaseOK g w cpu c) :
    PhaseOK (RestartWP.clearReservation g cpu) w cpu { c with fetch := i, reservation := none } := by
  cases phase : c.phase with
  | idle => trivial
  | reserved word => exact False.elim (family_not_reserved family word phase)
  | held B v t => simpa only [PhaseOK, phase, HeldFacts, Winning, RestartWP.clearReservation] using ok
  | loaded B v t => simpa only [PhaseOK, phase, HeldFacts, Winning, RestartWP.clearReservation] using ok
  | stored B v t => simpa only [PhaseOK, phase, HeldFacts, Winning, RestartWP.clearReservation] using ok

end MachCSL.Machine.SpinlockPool
