import MachCSL.Machine.SpinlockWitnessReleaseDefs

namespace MachCSL.Machine.SpinlockWitnessRelease
open MachCSL.Memory MachCSL.Machine.SpinlockWitness MachCSL.Machine.SpinlockWitnessHeld
attribute [local instance] SpinlockWitness.platform
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem failed_tail :
    pauseRun readFourView 2000 (swapResume 1 1#32 (.Ok none)) (pausedRegisters 1) = some (.pure (), failedRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem retry0 :
    fetchRun readFourView 2000 (cycle false) (retryAfter 0) = some ((), retryAfter 1) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem retry1 :
    fetchRun readFourView 2000 (cycle false) (retryAfter 1) = some ((), retryAfter 2) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem retry2 :
    fetchRun readFourView 2000 (cycle false) (retryAfter 2) = some ((), retryAfter 3) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem retry_result :
    retryResult = some (retryProgram, retryRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem retry_request :
    (readFour retryProgram).map Prod.fst = some (SpinlockAccess.readRequest .lock true) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem win_result (memory : ByteMap 64) :
    winResult memory = some (winProgram, retryRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem win_request :
    (writeFour winProgram).map Prod.fst = some (SpinlockAccess.writeRequest .lock true 1#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem win_tail :
    pauseRun readFiveView 2000 (winResume (.Ok none)) retryRegisters = some (.pure (), wonRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem second_work0 :
    fetchRun readFiveView 2000 (cycle false) (secondWork 0) = some ((), secondWork 1) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem second_work1 :
    fetchRun readFiveView 2000 (cycle false) (secondWork 1) = some ((), secondWork 2) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem second_work2 :
    fetchRun readFiveView 2000 (cycle false) (secondWork 2) = some ((), secondWork 3) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem second_work3 :
    fetchRun readFiveView 2000 (cycle false) (secondWork 3) = some ((), secondWork 4) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem increment_result :
    incrementResult = some (incrementProgram, incrementRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem increment_request :
    (writeFour incrementProgram).map Prod.fst = some (SpinlockAccess.writeRequest .counter false 2#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem increment_tail :
    pauseRun readSixView 2000 (incrementResume (.Ok none)) incrementRegisters = some (.pure (), incrementedRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem second_fence_result :
    secondFenceResult = some (secondFenceProgram, secondFenceRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem second_fence_kind :
    (barrierNext secondFenceProgram).map Prod.fst = some .Barrier_RISCV_rw_w := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem second_fence_tail :
    pauseRun readSixView 2000 (secondFenceResume ()) secondFenceRegisters = some (.pure (), secondFencedRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem release_result :
    releaseResult = some (releaseProgram, releaseRegisters) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem release_request :
    (writeFour releaseProgram).map Prod.fst = some (SpinlockAccess.writeRequest .lock false 0#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
    let some (_, _, rhs) := (← g.getType).eq? | throwError "expected equality"
    g.assign (← Lean.Meta.mkEqRefl rhs)

theorem memoryFour_lock : readBytes memoryFour SpinlockImage.lockAddress 4 = some 0#32 := rfl
theorem memoryFour_counter : readBytes memoryFour SpinlockImage.counterAddress 4 = some 1#32 := rfl
theorem memoryFive_lock : readBytes memoryFive SpinlockImage.lockAddress 4 = some 1#32 := rfl
theorem memoryFive_counter : readBytes memoryFive SpinlockImage.counterAddress 4 = some 1#32 := rfl
theorem memorySix_lock : readBytes memorySix SpinlockImage.lockAddress 4 = some 1#32 := rfl
theorem memorySix_counter : readBytes memorySix SpinlockImage.counterAddress 4 = some 2#32 := rfl
theorem memorySeven_lock : readBytes memorySeven SpinlockImage.lockAddress 4 = some 0#32 := rfl
theorem memorySeven_counter : readBytes memorySeven SpinlockImage.counterAddress 4 = some 2#32 := rfl

end MachCSL.Machine.SpinlockWitnessRelease
