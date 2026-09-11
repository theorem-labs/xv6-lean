import MachCSL.Machine.SpinlockDecodeDefs

namespace MachCSL.Machine.SpinlockDecode
open LeanPaperStock.Functions MachCSL.Logic.EventWP
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/- Each closed certificate is checked as a separate declaration. The tactic
constructs only `Eq.refl`; the declaration kernel verifies the full conversion.
This avoids the expensive preliminary `Meta.isDefEq` traversal of the generated
6000-line decoder. Keeping literals closed also avoids repeated conversions
under the dependent Fin case split. -/
private theorem decode00 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨0, by decide⟩)) =
      some (instruction ⟨0, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode01 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨1, by decide⟩)) =
      some (instruction ⟨1, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode02 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨2, by decide⟩)) =
      some (instruction ⟨2, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode03 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨3, by decide⟩)) =
      some (instruction ⟨3, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode04 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨4, by decide⟩)) =
      some (instruction ⟨4, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode05 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨5, by decide⟩)) =
      some (instruction ⟨5, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode06 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨6, by decide⟩)) =
      some (instruction ⟨6, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode07 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨7, by decide⟩)) =
      some (instruction ⟨7, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode08 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨8, by decide⟩)) =
      some (instruction ⟨8, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode09 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨9, by decide⟩)) =
      some (instruction ⟨9, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode10 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨10, by decide⟩)) =
      some (instruction ⟨10, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode11 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨11, by decide⟩)) =
      some (instruction ⟨11, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode12 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨12, by decide⟩)) =
      some (instruction ⟨12, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode13 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨13, by decide⟩)) =
      some (instruction ⟨13, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode14 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨14, by decide⟩)) =
      some (instruction ⟨14, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode15 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨15, by decide⟩)) =
      some (instruction ⟨15, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

private theorem decode16 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word ⟨16, by decide⟩)) =
      some (instruction ⟨16, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected an equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

/-- All seventeen literal opcodes are checked against the actual generated
`ext_decode` / `encdec_backwards`, including the CSR and AMO extension checks. -/
theorem decode_certificate (i : Fin 17) :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) decodeSnapshot 1000
      (ext_decode (SpinlockImage.word i)) = some (instruction i) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact decode00
  · exact decode01
  · exact decode02
  · exact decode03
  · exact decode04
  · exact decode05
  · exact decode06
  · exact decode07
  · exact decode08
  · exact decode09
  · exact decode10
  · exact decode11
  · exact decode12
  · exact decode13
  · exact decode14
  · exact decode15
  · exact decode16

theorem decodeSnapshot_covers (rs : RegisterFile)
    (priv : rs .cur_privilege = .Machine) (security : rs .mseccfg = 0#64)
    (misa : rs .misa = 0x800000000014112d#64) : JalLoop.Covers decodeSnapshot rs := by
  intro r value hv
  cases r <;> simp only [decodeSnapshot, JalLoop.decodeSnapshot, Option.some.injEq] at hv
  all_goals first | contradiction | subst value
  · exact security
  · exact misa
  · exact priv

/-- The actual generated decoder, for every word, using only owned reset fields.
No instruction execution or memory effect is asserted by this decoder plan. -/
theorem decode_plan (reads : ReadAllowed) (rs : RegisterFile) (i : Fin 17)
    (priv : rs .cur_privilege = .Machine) (security : rs .mseccfg = 0#64)
    (misa : rs .misa = 0x800000000014112d#64) :
    Returns reads rs (ext_decode (SpinlockImage.word i)) (instruction i) rs := by
  exact JalLoopPlan.snapshotPlanRun_plan reads (fun _ _ => none)
    (fun _ _ _ h => by cases h) decodeSnapshot rs
    (decodeSnapshot_covers rs priv security misa) 1000 _ _ (decode_certificate i)

end MachCSL.Machine.SpinlockDecode
