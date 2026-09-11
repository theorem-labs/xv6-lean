import MachCSL.Machine.SpinlockWitnessHeldDefs

namespace MachCSL.Machine.SpinlockWitnessHeld
open MachCSL.Memory MachCSL.Machine.SpinlockWitness
attribute [local instance] SpinlockWitness.platform
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/- Closed ordinary-kernel certificates, each checking actual generated code. -/
theorem swap0_result (memory : ByteMap 64) :
    swapResult 0 0#32 memory = some (swapProgram 0 0#32, pausedRegisters 0) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem swap0_request :
    (writeFour (swapProgram 0 0#32)).map Prod.fst =
      some (SpinlockAccess.writeRequest .lock true 1#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem swap1_result (memory : ByteMap 64) :
    swapResult 1 1#32 memory = some (swapProgram 1 1#32, pausedRegisters 1) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem swap1_request :
    (writeFour (swapProgram 1 1#32)).map Prod.fst =
      some (SpinlockAccess.writeRequest .lock true 1#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem swap_tail :
    pauseRun readOne 2000 (swapResume 0 0#32 (.Ok none)) (pausedRegisters 0) =
      some (.pure (), acquiredRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem work0 :
    fetchRun readOne 2000 (cycle false) (workAfter 0) = some ((), workAfter 1) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem work1 :
    fetchRun readOne 2000 (cycle false) (workAfter 1) = some ((), workAfter 2) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem work2 :
    fetchRun readOne 2000 (cycle false) (workAfter 2) = some ((), workAfter 3) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem work3 :
    fetchRun readOne 2000 (cycle false) (workAfter 3) = some ((), workAfter 4) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem counter_result : counterResult = some (counterProgram, counterRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem counter_request : (writeFour counterProgram).map Prod.fst =
    some (SpinlockAccess.writeRequest .counter false 1#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem fence_result : fenceResult = some (fenceProgram, fenceRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem fence_kind : (barrierNext fenceProgram).map Prod.fst =
    some .Barrier_RISCV_rw_w := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem unlock_result : unlockResult = some (unlockProgram, unlockRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem unlock_request : (writeFour unlockProgram).map Prod.fst =
    some (SpinlockAccess.writeRequest .lock false 0#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem counter_tail : pauseRun readTwo 2000 (counterResume (.Ok none)) counterRegisters =
    some (.pure (), storedRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem fence_tail : pauseRun readTwo 2000 (fenceResume ()) fenceRegisters =
    some (.pure (), fencedRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem memoryOne_lock : readBytes memoryOne SpinlockImage.lockAddress 4 = some 1#32 := rfl
theorem memoryOne_counter : readBytes memoryOne SpinlockImage.counterAddress 4 = some 0#32 := rfl
theorem memoryTwo_lock : readBytes memoryTwo SpinlockImage.lockAddress 4 = some 1#32 := rfl
theorem memoryTwo_counter : readBytes memoryTwo SpinlockImage.counterAddress 4 = some 1#32 := rfl

end MachCSL.Machine.SpinlockWitnessHeld
