import Xv6.Kernel.MycpuDecodeDefs

namespace Xv6.Kernel.MycpuDecode
open MachCSL.Machine LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem decode00 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨0, by decide⟩) 1000
      (decode ⟨0, by decide⟩) = some (decoded ⟨0, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode01 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨1, by decide⟩) 1000
      (decode ⟨1, by decide⟩) = some (decoded ⟨1, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode02 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨2, by decide⟩) 1000
      (decode ⟨2, by decide⟩) = some (decoded ⟨2, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode03 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨3, by decide⟩) 1000
      (decode ⟨3, by decide⟩) = some (decoded ⟨3, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode04 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨4, by decide⟩) 1000
      (decode ⟨4, by decide⟩) = some (decoded ⟨4, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode05 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨5, by decide⟩) 1000
      (decode ⟨5, by decide⟩) = some (decoded ⟨5, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode06 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨6, by decide⟩) 1000
      (decode ⟨6, by decide⟩) = some (decoded ⟨6, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode07 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨7, by decide⟩) 1000
      (decode ⟨7, by decide⟩) = some (decoded ⟨7, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode08 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨8, by decide⟩) 1000
      (decode ⟨8, by decide⟩) = some (decoded ⟨8, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode09 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨9, by decide⟩) 1000
      (decode ⟨9, by decide⟩) = some (decoded ⟨9, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode10 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨10, by decide⟩) 1000
      (decode ⟨10, by decide⟩) = some (decoded ⟨10, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode11 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨11, by decide⟩) 1000
      (decode ⟨11, by decide⟩) = some (decoded ⟨11, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode12 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨12, by decide⟩) 1000
      (decode ⟨12, by decide⟩) = some (decoded ⟨12, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode13 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨13, by decide⟩) 1000
      (decode ⟨13, by decide⟩) = some (decoded ⟨13, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

end Xv6.Kernel.MycpuDecode
