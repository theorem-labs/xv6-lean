import MachCSL.Machine.SpinlockScalarDefs

namespace MachCSL.Machine.SpinlockScalar
open LeanPaperStock.Functions MachCSL.Logic.EventWP
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem checked [Platform] (i : Fin 7) (rs : RegisterFile) :
    JalLoopPlan.registerPlanRun 100 (execute (SpinlockDecode.instruction (index i))) rs =
      some (.Retire_Success (), after i rs) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

theorem execute_plan [Platform] (reads : ReadAllowed) (i : Fin 7) (rs : RegisterFile) :
    Returns reads rs (execute (SpinlockDecode.instruction (index i)))
      (.Retire_Success ()) (after i rs) :=
  JalLoopPlan.registerPlanRun_plan reads 100 _ rs _ _ (checked i rs)

end MachCSL.Machine.SpinlockScalar
