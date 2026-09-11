import MachCSL.Machine.JalLoopPlanEval
import MachCSL.Machine.JalLoopInstruction

/-! Actual decode and JAL plans under scalar reset facts. All other register
contents remain arbitrary; the checked evaluator rejects hardware pin accesses. -/
namespace MachCSL.Machine.JalLoopPlan
open MachCSL.Logic.EventWP LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private theorem decode_checked :
    snapshotPlanRun (fun _ _ => none) JalLoop.decodeSnapshot 1000 (ext_decode 0x6f#32) =
      some (.JAL (0#21, .Regidx 0#5)) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

theorem decode_plan (reads : ReadAllowed) (rs : RegisterFile)
    (priv : rs .cur_privilege = .Machine) (security : rs .mseccfg = 0#64) :
    Returns reads rs (ext_decode 0x6f#32) (.JAL (0#21, .Regidx 0#5)) rs := by
  apply snapshotPlanRun_plan reads (fun _ _ => none) (fun _ _ _ h => by cases h)
    JalLoop.decodeSnapshot rs _ 1000 _ _ decode_checked
  intro r value hv
  cases r <;> simp only [JalLoop.decodeSnapshot, Option.some.injEq] at hv
  all_goals first | contradiction | subst value
  · exact security
  · exact priv

private def instructionStatic (base : RegisterFile) (r : Register) : RegisterType r :=
  match r with
  | .PC => jalImage.vector
  | .misa => 0x800000000014112d#64
  | other => base other

private theorem execute_checked [Platform] (base : RegisterFile) :
    registerPlanRun 100 (execute_JAL 0#21 (.Regidx 0#5)) (instructionStatic base) =
      some (.Retire_Success (), Sail.Registers.write (instructionStatic base) .nextPC jalImage.vector) := by
  cbv

private theorem instructionStatic_eq (base : RegisterFile)
    (pc : base .PC = jalImage.vector)
    (misa : base .misa = 0x800000000014112d#64) : instructionStatic base = base := by
  funext r
  cases r <;> simp only [instructionStatic, pc, misa]

theorem execute_JAL_plan [Platform] (reads : ReadAllowed) (rs : RegisterFile)
    (pc : rs .PC = jalImage.vector) (misa : rs .misa = 0x800000000014112d#64) :
    Returns reads rs (execute_JAL 0#21 (.Regidx 0#5)) (.Retire_Success ())
      (Sail.Registers.write rs .nextPC jalImage.vector) := by
  have checked := execute_checked rs
  rw [instructionStatic_eq rs pc misa] at checked
  exact registerPlanRun_plan reads _ _ _ _ _ checked

end MachCSL.Machine.JalLoopPlan
