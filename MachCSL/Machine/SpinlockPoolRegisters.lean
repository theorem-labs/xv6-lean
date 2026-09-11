import MachCSL.Machine.SpinlockPoolHead
import MachCSL.Logic.RegisterWPProofs
import MachCSL.Logic.RestartWPProofs

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan

theorem owned_match_write {physical symbolic} (same : OwnedMatch physical symbolic)
    (r : Register) (value : RegisterType r) :
    OwnedMatch (Sail.Registers.write physical r value) (Sail.Registers.write symbolic r value) := by
  intro s owned
  by_cases equal : r = s
  · subst s; simp only [Sail.Registers.write_same]
  · rw [Sail.Registers.write_other _ _ _ _ equal, Sail.Registers.write_other _ _ _ _ equal]
    exact same s owned

theorem owned_match_pin {physical symbolic} (same : OwnedMatch physical symbolic)
    (r : Register) (value : RegisterType r) (pin : EventWP.IsPin r) :
    OwnedMatch (Sail.Registers.write physical r value) symbolic := by
  intro s owned
  have different : r ≠ s := by intro equal; subst s; exact owned pin
  rw [Sail.Registers.write_other _ _ _ _ different]
  exact same s owned

/-- Transport through either owned or physical-pin register read, using the
actual primitive successor and the exact typed return value. -/
theorem read_transport [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (r : Register) (k : RegisterType r → SailM Unit)
    (control : CursorControl g cpu (.impure (.readReg r) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.readReg r) k)) g observations e' g' forks) :
    ∃ program', e' = .hart gen cpu program' ∧ g' = g ∧ observations = [] ∧ forks = [] ∧
      CursorEdge cpu c (.impure (.readReg r) k) c program' ∧ CursorControl g' cpu program' c := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    RegisterWP.read_step_unique _ g gen cpu r k live observations e' g' forks step
  rcases EventPlanHead.read_register_cases control.2.2 with ⟨owned, rest⟩ | ⟨pin, rest⟩
  · rw [control.1 r owned]
    exact ⟨_, rfl, rfl, rfl, rfl, .readOwned c r k owned, control.1, control.2.1, rest⟩
  · exact ⟨_, rfl, rfl, rfl, rfl, .readPin c r k pin _, control.1, control.2.1, rest _⟩

/-- An actual register write updates precisely the symbolic owned-cell model. -/
theorem write_transport [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (r : Register) (value : RegisterType r) (k : Unit → SailM Unit)
    (control : CursorControl g cpu (.impure (.writeReg r value) k) c)
    (live : ThreadLive g gen) {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.impure (.writeReg r value) k)) g observations e' g' forks) :
    ∃ c', e' = .hart gen cpu (k ()) ∧ observations = [] ∧ forks = [] ∧
      CursorEdge cpu c (.impure (.writeReg r value) k) c' (k ()) ∧ CursorControl g' cpu (k ()) c' := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    RegisterWP.write_step_unique _ g gen cpu r value k live observations e' g' forks step
  obtain ⟨owned, rest⟩ := EventPlanHead.write_register_cases control.2.2
  refine ⟨{ c with registers := Sail.Registers.write c.registers r value },
    rfl, rfl, rfl, .writeOwned c r value k owned, ?_, control.2.1, rest⟩
  change OwnedMatch (updateHart g.registers cpu (Sail.Registers.write (g.registers cpu) r value) cpu) _
  simpa only [updateHart, ite_true] using owned_match_write control.1 r value

/-- Every actual restart selects either existing cycle plan and clears rr. -/
theorem restart_transport [Platform] {g g' : State} {gen : Nat} {cpu : CPU} {c : Cursor}
    (control : CursorControl g cpu (.pure ()) c) (live : ThreadLive g gen)
    {observations e' forks}
    (step : Step SpinlockImage.image (.hart gen cpu (.pure ())) g observations e' g' forks) :
    ∃ tick c', e' = .hart gen cpu (cycle tick) ∧ observations = [] ∧ forks = [] ∧
      CursorEdge cpu c (.pure ()) c' (cycle tick) ∧ CursorControl g' cpu (cycle tick) c' := by
  obtain ⟨tick, rfl, rfl, rfl, rfl⟩ :=
    RestartWP.restart_successors _ g gen cpu live observations e' g' forks step
  obtain ⟨i, family⟩ := EventPlanHead.pure_iff.mp control.2.2
  refine ⟨tick, { c with fetch := i, reservation := none }, rfl, rfl, rfl,
    .restart c i tick family, control.1, ?_, SpinlockFamily.cycle_plan i family none tick⟩
  simp [RestartWP.clearReservation, updateHart]

/-- Both actual PLIC arms preserve each cursor's partial register agreement. -/
theorem plic_control (g : State) (files : CPU → RegisterFile)
    (step : PlicStep g.devices g.registers files) (cpu : CPU) (program : SailM Unit) (c : Cursor)
    (control : CursorControl g cpu program c) :
    CursorControl { g with registers := files } cpu program c := by
  refine ⟨?_, control.2⟩
  cases step with
  | supervisor selected =>
    by_cases equal : cpu = selected
    · subst cpu
      simp only [updateHart, ite_true]
      exact owned_match_pin control.1 .sig_seip _ (Or.inl rfl)
    · simpa only [updateHart, if_neg equal] using control.1
  | machine selected =>
    by_cases equal : cpu = selected
    · subst cpu
      simp only [updateHart, ite_true]
      exact owned_match_pin control.1 .sig_meip _ (Or.inr rfl)
    · simpa only [updateHart, if_neg equal] using control.1

end MachCSL.Machine.SpinlockPool
