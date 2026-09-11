import MachCSL.Machine.SpinlockCycleDefs

namespace MachCSL.Machine.SpinlockCycle
open LeanPaperStock.Functions MachCSL.Logic
open MachCSL.Logic.EventWP
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

private theorem prefixPlan {S A B : Type} {reads : ReadAllowed} {rel : EventPlan.Relations S}
    {rs rr s middle value} {program : SailM A} {next : A → SailM B}
    {Q : B → RegisterFile → Option Reservation → S → Prop}
    (first : EventWP.Returns reads rs program value middle)
    (rest : EventPlan.Plan reads rel middle rr s (next value) Q) :
    EventPlan.Plan reads rel rs rr s (program >>= next) Q :=
  EventPlan.Plan.bind (EventPlan.of_returns first)
    (fun _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩ => rest)

/-- Actual active-hart wrapper around a separately proved interruptible
instruction. The instruction plan covers every returned protocol branch. -/
theorem active_plan [Platform] {S : Type} (i : Fin 17) (rel : EventPlan.Relations S)
    (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : SpinlockFetch.Static i rs) (off : BootPmp.Off rs)
    (Q : RegisterFile → Option Reservation → S → Prop)
    (executed : EventPlan.Plan (SpinlockFetch.CodeRead i) rel (prepare rs) rr s
      (execute (SpinlockDecode.instruction i))
      (fun result after rr' next => result = .Retire_Success () ∧ Q after rr' next)) :
    EventPlan.Plan (SpinlockFetch.CodeRead i) rel rs rr s (run_hart_active 0)
    (fun result after rr' next =>
        result = .Step_Execute (.Retire_Success (), SpinlockImage.word i) ∧ Q after rr' next) := by
  let reads := SpinlockFetch.CodeRead i
  have landing : EventWP.Returns reads rs (is_landing_pad_expected ()) false rs := by
    unfold is_landing_pad_expected
    refine (read_plan reads rs .elp (by decide)).bind ?_
    rw [static.elp]
    exact pure_plan reads rs false
  unfold run_hart_active _root_.Sail.SailME.run PreSail.PreSailME.run
  apply EventPlan.Plan.bind (P := fun result after rr' next =>
    result = Except.ok (.Step_Execute (.Retire_Success (), SpinlockImage.word i)) ∧ Q after rr' next)
  · refine prefixPlan ((read_plan reads rs .cur_privilege (by decide)).liftExcept _root_.Step) ?_
    change EventPlan.Plan reads rel rs rr s (_ >>= _) _
    rw [static.privilege]
    refine prefixPlan ((JalLoopPlan.dispatchInterrupt_plan reads rs static.mstatus).liftExcept _root_.Step) ?_
    refine prefixPlan ((SpinlockFetch.universal_fetch_plan i rs static off).liftExcept _root_.Step) ?_
    refine prefixPlan ((SpinlockDecode.decode_plan reads rs i static.privilege static.mseccfg static.misa).liftExcept _root_.Step) ?_
    simp only [show get_config_print_instr () = false from rfl, Bool.false_eq_true, ↓reduceIte]
    refine prefixPlan (landing.liftExcept _root_.Step) ?_
    refine prefixPlan ((read_plan reads rs .PC (by decide)).liftExcept _root_.Step) ?_
    refine prefixPlan ((write_plan reads rs .nextPC (Sail.BitVec.addInt (rs .PC) 4) (by decide)).liftExcept _root_.Step) ?_
    simp only [ExceptT.bindCont]
    apply EventPlan.Plan.exceptBind (P := fun result after rr' next =>
      result = .Retire_Success () ∧ Q after rr' next)
    · apply EventPlan.Plan.exceptBind (executed.liftExcept _root_.Step)
      intro result after rr' next h
      rcases h with ⟨rfl, good⟩
      exact .pure ⟨.Retire_Success (), rfl, rfl, good⟩
    · intro result after rr' next h
      rcases h with ⟨rfl, good⟩
      exact .pure ⟨rfl, good⟩
  · intro result after rr' next h
    rcases h with ⟨rfl, good⟩
    exact .pure ⟨rfl, good⟩

theorem tick_pc_plan (reads : ReadAllowed) (rs : RegisterFile) :
    EventWP.Returns reads rs (tick_pc ()) () (tickPC rs) := by
  unfold tick_pc
  refine (read_plan reads rs .nextPC (by decide)).bind ?_
  refine (write_plan reads rs .PC (rs .nextPC) (by decide)).bind ?_
  refine (read_plan reads (tickPC rs) .PC (by decide)).bind ?_
  exact pure_plan reads _ ()

theorem static_enable (i : Fin 17) (rs : RegisterFile) (static : SpinlockFetch.Static i rs) :
    SpinlockFetch.Static i (JalLoopPlan.enableAfter rs) :=
  ⟨static.pc, static.nextPC, static.misa, static.mstatus, static.mie, static.mideleg,
    static.menvcfg, static.elp, static.mseccfg, static.privilege, static.hartState, static.pma, static.htif⟩

theorem try_step_plan [Platform] {S : Type} (i : Fin 17) (rel : EventPlan.Relations S)
    (rs : RegisterFile) (rr : Option Reservation) (s : S)
    (static : SpinlockFetch.Static i rs) (off : BootPmp.Off rs)
    (Q : RegisterFile → Option Reservation → S → Prop)
    (executed : EventPlan.Plan (SpinlockFetch.CodeRead i) rel (prepare (JalLoopPlan.enableAfter rs)) rr s
      (execute (SpinlockDecode.instruction i))
      (fun result after rr' next => result = .Retire_Success () ∧
        after .hart_state = .HART_ACTIVE () ∧ Q after rr' next)) :
    EventPlan.Plan (SpinlockFetch.CodeRead i) rel rs rr s (try_step 0 false)
      (fun result after rr' next => result = false ∧
        ∃ completed, Q completed rr' next ∧ after = retire (tickPC completed)) := by
  let reads := SpinlockFetch.CodeRead i
  unfold try_step
  refine prefixPlan (read_plan reads rs .cur_privilege (by decide)) ?_
  refine prefixPlan (JalLoopPlan.should_inc_minstret_plan reads rs (rs .cur_privilege)) ?_
  refine prefixPlan (write_plan reads rs .minstret_increment (JalLoopPlan.retireEnabled rs) (by decide)) ?_
  let middle := JalLoopPlan.enableAfter rs
  have st : SpinlockFetch.Static i middle := static_enable i rs static
  rw [BootPmp.sail_bind_assoc]
  refine prefixPlan (read_plan reads middle .hart_state (by decide)) ?_
  rw [st.hartState]
  apply EventPlan.Plan.bind (active_plan i rel middle rr s st off
    (fun after rr' next => after .hart_state = .HART_ACTIVE () ∧ Q after rr' next) executed)
  intro value after rr' next h
  rcases h with ⟨rfl, active, good⟩
  refine prefixPlan (read_plan reads after .hart_state (by decide)) ?_
  rw [active]
  refine prefixPlan (pure_plan reads after ()) ?_
  refine prefixPlan (read_plan reads after .hart_state (by decide)) ?_
  rw [active]
  refine prefixPlan (tick_pc_plan reads after) ?_
  refine prefixPlan (read_plan reads (tickPC after) .minstret_increment (by decide)) ?_
  change EventPlan.Plan reads rel (tickPC after) rr' next
    (if (tickPC after) .minstret_increment then
      (do Sail.ConcurrencyInterfaceV1.Free.PreSail.writeReg .minstret
            (Sail.BitVec.addInt (← Sail.ConcurrencyInterfaceV1.Free.PreSail.readReg .minstret) 1)
          pure false)
     else pure false) _
  cases enabled : (tickPC after) .minstret_increment
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact .pure ⟨rfl, after, good, by simp only [retire, enabled, Bool.false_eq_true, ↓reduceIte]⟩
  · simp only [↓reduceIte]
    refine prefixPlan (read_plan reads (tickPC after) .minstret (by decide)) ?_
    refine prefixPlan (write_plan reads (tickPC after) .minstret
      (Sail.BitVec.addInt ((tickPC after) .minstret) 1) (by decide)) ?_
    exact .pure ⟨rfl, after, good, by simp only [retire, enabled, ↓reduceIte]⟩

theorem cycle_plan [Platform] {S : Type} (i : Fin 17) (rel : EventPlan.Relations S)
    (rs : RegisterFile) (rr : Option Reservation) (s : S) (tick : Bool)
    (static : SpinlockFetch.Static i rs) (off : BootPmp.Off rs)
    (Q : RegisterFile → Option Reservation → S → Prop)
    (executed : EventPlan.Plan (SpinlockFetch.CodeRead i) rel (prepare (JalLoopPlan.enableAfter rs)) rr s
      (execute (SpinlockDecode.instruction i))
      (fun result after rr' next => result = .Retire_Success () ∧
        after .hart_state = .HART_ACTIVE () ∧ after .menvcfg = 0#64 ∧ Q after rr' next)) :
    EventPlan.Plan (SpinlockFetch.CodeRead i) rel rs rr s (cycle tick)
      (fun _ after rr' next => ∃ completed, Q completed rr' next ∧ after = finish tick completed) := by
  let reads := SpinlockFetch.CodeRead i
  unfold cycle
  apply EventPlan.Plan.bind (try_step_plan i rel rs rr s static off
    (fun after rr' next => after .menvcfg = 0#64 ∧ Q after rr' next) executed)
  intro result after rr' next h
  rcases h with ⟨rfl, completed, ⟨env, good⟩, rfl⟩
  cases tick
  · exact .pure ⟨completed, good, rfl⟩
  · have unchanged : (retire (tickPC completed)) .menvcfg = 0#64 := by
      unfold retire
      split <;> exact env
    apply (EventPlan.of_returns
      (JalLoopPlan.tick_clock_plan reads (retire (tickPC completed)) unchanged)).mono
    rintro _ _ _ _ ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨completed, good, rfl⟩

end MachCSL.Machine.SpinlockCycle
