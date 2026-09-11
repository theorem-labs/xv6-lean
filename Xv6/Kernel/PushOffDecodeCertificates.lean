import Xv6.Kernel.PushOffDecodeSpec
import Xv6.Kernel.MycpuDecodeCertificates

namespace Xv6.Kernel.PushOffDecode
open MachCSL.Machine LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/- Each new certificate is ordinary Eq.refl checked by the declaration kernel.
The tactic only constructs that proof term; it does not evaluate native code.
Three JALs are handled separately by the generic bitfield decoder factor. -/

theorem decode00 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨0, by decide⟩) 1000
      (program ⟨0, by decide⟩) = some (PushOffCode.decoded ⟨0, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode01 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨1, by decide⟩) 1000
      (program ⟨1, by decide⟩) = some (PushOffCode.decoded ⟨1, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode02 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨2, by decide⟩) 1000
      (program ⟨2, by decide⟩) = some (PushOffCode.decoded ⟨2, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode03 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨3, by decide⟩) 1000
      (program ⟨3, by decide⟩) = some (PushOffCode.decoded ⟨3, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode04 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨4, by decide⟩) 1000
      (program ⟨4, by decide⟩) = some (PushOffCode.decoded ⟨4, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode05 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨5, by decide⟩) 1000
      (program ⟨5, by decide⟩) = some (PushOffCode.decoded ⟨5, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode06 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨6, by decide⟩) 1000
      (program ⟨6, by decide⟩) = some (PushOffCode.decoded ⟨6, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode08 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨8, by decide⟩) 1000
      (program ⟨8, by decide⟩) = some (PushOffCode.decoded ⟨8, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode09 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨9, by decide⟩) 1000
      (program ⟨9, by decide⟩) = some (PushOffCode.decoded ⟨9, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode11 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨11, by decide⟩) 1000
      (program ⟨11, by decide⟩) = some (PushOffCode.decoded ⟨11, by decide⟩) := by
  exact decode08

theorem decode12 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨12, by decide⟩) 1000
      (program ⟨12, by decide⟩) = some (PushOffCode.decoded ⟨12, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode13 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨13, by decide⟩) 1000
      (program ⟨13, by decide⟩) = some (PushOffCode.decoded ⟨13, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode14 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨14, by decide⟩) 1000
      (program ⟨14, by decide⟩) = some (PushOffCode.decoded ⟨14, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode15 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨15, by decide⟩) 1000
      (program ⟨15, by decide⟩) = some (PushOffCode.decoded ⟨15, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode16 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨16, by decide⟩) 1000
      (program ⟨16, by decide⟩) = some (PushOffCode.decoded ⟨16, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode17 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨17, by decide⟩) 1000
      (program ⟨17, by decide⟩) = some (PushOffCode.decoded ⟨17, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode18 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨18, by decide⟩) 1000
      (program ⟨18, by decide⟩) = some (PushOffCode.decoded ⟨18, by decide⟩) := by
  exact MycpuDecode.decode13

theorem decode20 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨20, by decide⟩) 1000
      (program ⟨20, by decide⟩) = some (PushOffCode.decoded ⟨20, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode21 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨21, by decide⟩) 1000
      (program ⟨21, by decide⟩) = some (PushOffCode.decoded ⟨21, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode22 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨22, by decide⟩) 1000
      (program ⟨22, by decide⟩) = some (PushOffCode.decoded ⟨22, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem decode23 :
    JalLoopPlan.snapshotPlanRun (fun _ _ => none) (snapshot ⟨23, by decide⟩) 1000
      (program ⟨23, by decide⟩) = some (PushOffCode.decoded ⟨23, by decide⟩) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

end Xv6.Kernel.PushOffDecode
