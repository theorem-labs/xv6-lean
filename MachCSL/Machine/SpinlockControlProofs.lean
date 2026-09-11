import MachCSL.Machine.SpinlockControlDefs

namespace MachCSL.Machine.SpinlockControl
open LeanPaperStock.Functions MachCSL.Logic.EventWP
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem csr_checked [Platform] (rs : RegisterFile) :
    JalLoopPlan.registerPlanRun 100
      (execute (SpinlockDecode.instruction ⟨0, by decide⟩)) (csrStatic rs) =
      some (.Retire_Success (), csrAfter (csrStatic rs)) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem csrStatic_eq (rs : RegisterFile) (priv : rs .cur_privilege = .Machine) : csrStatic rs = rs := by
  funext r
  cases r <;> simp only [csrStatic, priv]

theorem csr_plan [Platform] (reads : ReadAllowed) (rs : RegisterFile)
    (priv : rs .cur_privilege = .Machine) :
    Returns reads rs (execute (SpinlockDecode.instruction ⟨0, by decide⟩))
      (.Retire_Success ()) (csrAfter rs) := by
  have checked := csr_checked rs
  rw [csrStatic_eq rs priv] at checked
  exact JalLoopPlan.registerPlanRun_plan reads 100 _ rs _ _ checked

private theorem jump_checked [Platform] (i : Fin 17) (rs : RegisterFile) :
    JalLoopPlan.registerPlanRun 100 (jump_to (SpinlockImage.instructionAddress i)) (jumpStatic rs) =
      some (.Retire_Success (), Sail.Registers.write (jumpStatic rs) .nextPC (SpinlockImage.instructionAddress i)) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

theorem jumpStatic_eq (rs : RegisterFile) (misa : rs .misa = 0x800000000014112d#64) : jumpStatic rs = rs := by
  funext r
  cases r <;> simp only [jumpStatic, misa]

theorem jump_plan [Platform] (reads : ReadAllowed) (i : Fin 17) (rs : RegisterFile)
    (misa : rs .misa = 0x800000000014112d#64) :
    Returns reads rs (jump_to (SpinlockImage.instructionAddress i)) (.Retire_Success ())
      (Sail.Registers.write rs .nextPC (SpinlockImage.instructionAddress i)) := by
  have checked := jump_checked i rs
  rw [jumpStatic_eq rs misa] at checked
  exact JalLoopPlan.registerPlanRun_plan reads 100 _ rs _ _ checked

theorem select_branch_plan [Platform] (reads : ReadAllowed) (rs : RegisterFile)
    (pc : rs .PC = SpinlockImage.instructionAddress ⟨2, by decide⟩)
    (misa : rs .misa = 0x800000000014112d#64) :
    Returns reads rs (execute (SpinlockDecode.instruction ⟨2, by decide⟩))
      (.Retire_Success ()) (branchAfter false rs) := by
  change Returns reads rs
    (do let value ← Sail.readReg .x6
        if value == 0#64 then jump_to ((← Sail.readReg .PC) + sign_extend (m := 64) 0x38#13)
        else pure (.Retire_Success ())) _ _
  refine (read_plan reads rs .x6 (by decide)).bind ?_
  cases test : rs .x6 == 0#64
  · simp only [test, Bool.false_eq_true, ↓reduceIte, branchAfter, Bool.false_eq_true]
    exact pure_plan reads rs _
  · simp only [test, ↓reduceIte, branchAfter]
    refine (read_plan reads rs .PC (by decide)).bind ?_
    rw [pc]
    exact jump_plan reads ⟨16, by decide⟩ rs misa

theorem retry_branch_plan [Platform] (reads : ReadAllowed) (rs : RegisterFile)
    (pc : rs .PC = SpinlockImage.instructionAddress ⟨9, by decide⟩)
    (misa : rs .misa = 0x800000000014112d#64) :
    Returns reads rs (execute (SpinlockDecode.instruction ⟨9, by decide⟩))
      (.Retire_Success ()) (branchAfter true rs) := by
  change Returns reads rs
    (do let value ← Sail.readReg .x15
        if value != 0#64 then jump_to ((← Sail.readReg .PC) + sign_extend (m := 64) 0x1ff4#13)
        else pure (.Retire_Success ())) _ _
  refine (read_plan reads rs .x15 (by decide)).bind ?_
  cases test : rs .x15 != 0#64
  · simp only [test, Bool.false_eq_true, ↓reduceIte, branchAfter]
    exact pure_plan reads rs _
  · simp only [test, ↓reduceIte, branchAfter]
    refine (read_plan reads rs .PC (by decide)).bind ?_
    rw [pc]
    have target : SpinlockImage.instructionAddress ⟨9, by decide⟩ + sign_extend (m := 64) 0x1ff4#13 =
        SpinlockImage.instructionAddress ⟨6, by decide⟩ := by
      run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
        let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
        g.assign (← Lean.Meta.mkEqRefl rhs)
    rw [target]
    exact jump_plan reads ⟨6, by decide⟩ rs misa

theorem jal_zero_plan [Platform] (reads : ReadAllowed) (rs : RegisterFile)
    (imm : BitVec 21) (target : Fin 17)
    (address : rs .PC + sign_extend (m := 64) imm = SpinlockImage.instructionAddress target)
    (misa : rs .misa = 0x800000000014112d#64) :
    Returns reads rs (execute_JAL imm (.Regidx 0#5)) (.Retire_Success ())
      (Sail.Registers.write rs .nextPC (SpinlockImage.instructionAddress target)) := by
  unfold execute_JAL
  refine (read_plan reads rs .nextPC (by decide)).bind ?_
  refine (read_plan reads rs .PC (by decide)).bind ?_
  rw [address]
  refine (jump_plan reads target rs misa).bind ?_
  exact pure_plan reads _ _

theorem loop_jump_plan [Platform] (reads : ReadAllowed) (rs : RegisterFile)
    (pc : rs .PC = SpinlockImage.instructionAddress ⟨15, by decide⟩)
    (misa : rs .misa = 0x800000000014112d#64) :
    Returns reads rs (execute (SpinlockDecode.instruction ⟨15, by decide⟩)) (.Retire_Success ())
      (Sail.Registers.write rs .nextPC (SpinlockImage.instructionAddress ⟨6, by decide⟩)) := by
  apply jal_zero_plan reads rs 0x1fffdc#21 ⟨6, by decide⟩ ?_ misa
  rw [pc]
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem park_jump_plan [Platform] (reads : ReadAllowed) (rs : RegisterFile)
    (pc : rs .PC = SpinlockImage.instructionAddress ⟨16, by decide⟩)
    (misa : rs .misa = 0x800000000014112d#64) :
    Returns reads rs (execute (SpinlockDecode.instruction ⟨16, by decide⟩)) (.Retire_Success ())
      (Sail.Registers.write rs .nextPC (SpinlockImage.instructionAddress ⟨16, by decide⟩)) := by
  apply jal_zero_plan reads rs 0#21 ⟨16, by decide⟩ ?_ misa
  rw [pc]
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

end MachCSL.Machine.SpinlockControl
