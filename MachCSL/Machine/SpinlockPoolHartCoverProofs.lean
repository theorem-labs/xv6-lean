import MachCSL.Machine.SpinlockPoolCoverHelpers

namespace MachCSL.Machine.SpinlockPool
open Memory Logic Logic.EventPlan Logic.SpinlockProtocol

theorem cover_live_hart [Platform] {left right : Pool} {g g' : State} {gen : Nat} {cpu : CPU}
    {program : SailM Unit} {c : Cursor} {observations : List Observation} {e' : Expr} {forks : List Expr}
    (inv : PoolInv (left ++ (.hart gen cpu program, .hart c) :: right, g))
    (live : ThreadLive g gen)
    (step : Step SpinlockImage.image (.hart gen cpu program) g observations e' g' forks) :
    Covered left right (.hart gen cpu program) (.hart c) g observations e' g' forks := by
  obtain ⟨memory, reservations, image, reset, code, w, words, locals, owner⟩ := inv.2 live.1
  obtain ⟨control, ok⟩ := locals gen cpu program c
    (List.mem_append_right _ (List.mem_cons_self ..)) live
  have self : ∀ B, w.owner = some (cpu, B) → HolderPosition c.phase = some B :=
    fun _ owned => selected_owner_phase inv.1 live owner owned
  cases EventPlanHead.head_of_plan control.2.2 with
  | pure good =>
    obtain ⟨tick, rfl, rfl, rfl, rfl⟩ :=
      RestartWP.restart_successors _ g gen cpu live observations e' g' forks step
    obtain ⟨i, family⟩ := good
    let after : Cursor := { c with fetch := i, reservation := none }
    have afterControl : CursorControl (RestartWP.clearReservation g cpu) cpu (cycle tick) after := by
      refine ⟨control.1, ?_, SpinlockFamily.cycle_plan i family none tick⟩
      simp [after, RestartWP.clearReservation, updateHart]
    exact covered_of_nonwrite inv live control locals owner step rfl rfl
      (.hart live (.restart c i tick family) (update_restart g cpu c i family.pc))
      afterControl (restart_phase family ok) words rfl
  | readOwned owned rest =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      RegisterWP.read_step_unique _ g gen cpu _ _ live observations e' g' forks step
    obtain ⟨program', target, noForks, transition, after⟩ := read_transition _ _ control live step
    exact covered_of_nonwrite inv live control locals owner step target noForks transition after ok words rfl
  | readPin pin rest =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      RegisterWP.read_step_unique _ g gen cpu _ _ live observations e' g' forks step
    obtain ⟨program', target, noForks, transition, after⟩ := read_transition _ _ control live step
    exact covered_of_nonwrite inv live control locals owner step target noForks transition after ok words rfl
  | writeOwned owned rest =>
    rename_i r value k
    obtain ⟨rfl, rfl, rfl, rfl⟩ :=
      RegisterWP.write_step_unique _ g gen cpu r value k live observations e' g' forks step
    have afterOk : PhaseOK (EraState.writeRegister g cpu r value) w cpu
        { c with registers := Sail.Registers.write c.registers r value } := ok
    apply covered_of_nonwrite inv live control locals owner step rfl rfl
      (.hart live (.writeOwned c r value k owned) (update_write_register g cpu c r value k owned))
      ⟨?_, control.2.1, rest⟩ afterOk words rfl
    change OwnedMatch (updateHart g.registers cpu (Sail.Registers.write (g.registers cpu) r value) cpu) _
    simpa only [updateHart, ite_true] using owned_match_write control.1 r value
  | codeRead ram plain allowed rest =>
    obtain ⟨view, lower, upper, state, target, noForks, transition, after, afterOk, afterWords⟩ :=
      code_transition w words ok image code _ _ _ allowed ram plain _ control live step
    exact covered_of_nonwrite inv live control locals owner step target noForks transition after afterOk afterWords rfl
  | plain enabled ram kind rest =>
    obtain ⟨word, next, related⟩ := enabled
    generalize phase : c.phase = s at related
    cases related with
    | load B v t =>
      obtain ⟨view, lower, upper, state, target, noForks, transition, after, afterOk, afterWords⟩ :=
        counter_transition w words ok B v t phase _ control live step
      exact covered_of_nonwrite inv live control locals owner step target noForks transition after afterOk afterWords rfl
  | exclusive enabled ram kind rest =>
    obtain ⟨idle, request⟩ := enabled
    have size := (Sigma.mk.inj request).1
    cases size
    have req := eq_of_heq (Sigma.mk.inj request).2
    cases req
    obtain ⟨program', c', target, noForks, transition, after, afterOk, afterWords⟩ :=
      exclusive_transition w words memory _ control live step
    exact covered_of_nonwrite inv live control locals owner step target noForks transition after afterOk afterWords rfl
  | write enabled present ram mode eligible rest =>
    generalize phase : c.phase = s at eligible
    generalize reservation : c.reservation = rr at mode eligible
    cases eligible with
    | swap old bound =>
      obtain ⟨program', c', w', target, noForks, transition, after, afterOk, afterWords, effect⟩ :=
        reserved_swap_transition w words memory reservations old phase ok _ control live step
      exact covered_of_selected inv live control locals owner step target noForks transition after afterOk afterWords
        (swap_owner_facts phase self effect)
    | increment B v t rr =>
      obtain ⟨program', c', w', target, noForks, transition, after, afterOk, afterWords, effect⟩ :=
        counter_store_transition w words ok B v t phase _ control live step
      exact covered_of_selected inv live control locals owner step target noForks transition after afterOk afterWords
        (counter_owner_facts self effect)
    | release B v t rr =>
      obtain ⟨program', c', w', target, noForks, transition, after, afterOk, afterWords, effect⟩ :=
        unlock_transition w words ok B v t phase _ control live step
      exact covered_of_selected inv live control locals owner step target noForks transition after afterOk afterWords
        (unlock_owner_facts self effect)
  | barrier enabled rest =>
    obtain ⟨next, related⟩ := enabled
    generalize phase : c.phase = s at related
    cases related with
    | fence B v t =>
      obtain ⟨target, state, noForks, transition, after, afterOk, afterWords⟩ :=
        fence_transition w words ok _ control live step
      exact covered_of_nonwrite inv live control locals owner step target noForks transition after afterOk afterWords rfl

end MachCSL.Machine.SpinlockPool
