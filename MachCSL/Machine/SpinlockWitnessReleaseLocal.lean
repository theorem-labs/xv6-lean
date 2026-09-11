import MachCSL.Machine.SpinlockWitnessReleaseState
import MachCSL.Machine.SpinlockWitnessReleaseCertificates

namespace MachCSL.Machine.SpinlockWitnessRelease
open MachCSL.Memory MachCSL.Machine.SpinlockWitness MachCSL.Machine.SpinlockWitnessHeld
attribute [local instance] SpinlockWitness.platform
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem reader_program (program : SailM Unit) (req : ReadRequest 4)
    (h : (readFour program).map Prod.fst = some req) :
    program = .impure (.readMem 4 req) (reader program).2 := by
  cases found : readFour program with
  | none => simp [found] at h
  | some pair =>
    have same : pair.1 = req := by simpa only [found, Option.map_some, Option.some.injEq] using h
    have exactProgram := readFour_program program pair.1 pair.2 found
    simp only [reader, found, Option.getD_some]
    exact exactProgram.trans
      (congrArg (fun q : ReadRequest 4 => (.impure (.readMem 4 q) pair.2 : SailM Unit)) same)

theorem failed_commit (devices : Devices.State) (others : PhysicalAddress → Prop)
    (free : Disjoint (Footprint SpinlockImage.lockAddress 4) others) :
    NodeStep Devices.bus others 1 (loadedRam SpinlockImage.image)
      (readerLocal devices) (swapProgram 1 1#32) (swapResume 1 1#32 (.Ok none)) (failedLocal devices) := by
  rw [writer_program _ _ swap1_request]
  exact write_node Devices.bus others 1 (loadedRam SpinlockImage.image)
    (readerLocal devices) (SpinlockAccess.writeRequest .lock true 1#32) 1#32
    (swapResume 1 1#32) rfl rfl free

theorem first_release (devices : Devices.State) (others : PhysicalAddress → Prop)
    (free : Disjoint (Footprint SpinlockImage.lockAddress 4) others) :
    NodeStep Devices.bus others 0 (loadedRam SpinlockImage.image)
      (firstReleaseLocal devices) unlockProgram (unlockResume (.Ok none)) (releasedLocal devices) := by
  rw [writer_program _ _ unlock_request]
  exact write_node Devices.bus others 0 (loadedRam SpinlockImage.image)
    (firstReleaseLocal devices) (SpinlockAccess.writeRequest .lock false 0#32) 0#32 unlockResume rfl rfl free

theorem retry_step (n : Nat) (bound : n < 3) :
    fetchRun readFourView 2000 (cycle false) (retryAfter n) = some ((), retryAfter (n + 1)) := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · exact retry0
  · exact retry1
  · exact retry2

theorem retry_all (n : Nat) (bound : n ≤ 3) :
    cyclesRun readFourView 2000 failedRegisters n = some (retryAfter n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have earlier := ih (by omega)
    have next := retry_step n (by omega)
    change (do
      let rs ← cyclesRun readFourView 2000 failedRegisters n
      let (_, after) ← fetchRun readFourView 2000 (cycle false) rs
      pure after) = _
    rw [earlier]
    change (fetchRun readFourView 2000 (cycle false) (retryAfter n) >>= fun (_, after) => some after) = _
    rw [next]
    rfl

theorem advance_retry (devices : Devices.State) (others : PhysicalAddress → Prop) :
    NodeSteps Devices.bus others 1 (loadedRam SpinlockImage.image)
      (swapResume 1 1#32 (.Ok none)) (retryStartLocal devices) retryProgram (retryLocal devices) := by
  let afterFail := { retryStartLocal devices with registers := failedRegisters }
  let afterRetry := { retryStartLocal devices with registers := retryAfter 3 }
  have finish := pauseRun_sound Devices.bus others 1 (loadedRam SpinlockImage.image) readFourView 2000
    _ (retryStartLocal devices) (.pure ()) failedRegisters (show 3 ≤ 4 from by decide) (fun _ => rfl) failed_tail
  have work := cyclesRun_sound Devices.bus others 1 (loadedRam SpinlockImage.image) readFourView 2000 3
    afterFail (retryAfter 3) (show 3 ≤ 4 from by decide) (fun _ => rfl) rfl (retry_all 3 (by decide))
  have next := pauseRun_sound Devices.bus others 1 (loadedRam SpinlockImage.image) readFourView 2000
    (cycle false) afterRetry retryProgram retryRegisters (show 3 ≤ 4 from by decide) (fun _ => rfl) retry_result
  have restart : NodeStep Devices.bus others 1 (loadedRam SpinlockImage.image)
      afterRetry (.pure ()) (cycle false) afterRetry := restart_step Devices.bus others _ _ afterRetry false
  exact nodeSteps_trans finish (nodeSteps_trans work (.cons restart next))

theorem retry_read (devices : Devices.State) (others : PhysicalAddress → Prop)
    (free : Disjoint (Footprint SpinlockImage.lockAddress 4) others) :
    NodeStep Devices.bus others 1 (loadedRam SpinlockImage.image)
      (retryLocal devices) retryProgram (retryResume (.Ok (0#32, none))) (retryReadLocal devices) := by
  rw [reader_program _ _ retry_request]
  exact read_exclusive_node Devices.bus others 1 (loadedRam SpinlockImage.image)
    (retryLocal devices) (SpinlockAccess.readRequest .lock true) 0#32 retryResume
    rfl rfl free memoryFour_lock

theorem win_prefix (devices : Devices.State) (others : PhysicalAddress → Prop) :
    NodeSteps Devices.bus others 1 (loadedRam SpinlockImage.image)
      (retryResume (.Ok (0#32, none))) (retryReadLocal devices) winProgram (retryReadLocal devices) := by
  exact pauseRun_sound Devices.bus others 1 (loadedRam SpinlockImage.image)
    (read (loadedRam SpinlockImage.image) logFour 1 4) 2000 _ (retryReadLocal devices) _ retryRegisters
    (Nat.le_refl 4) (fun _ => rfl) (win_result _)

theorem win_commit (devices : Devices.State) (others : PhysicalAddress → Prop)
    (free : Disjoint (Footprint SpinlockImage.lockAddress 4) others) :
    NodeStep Devices.bus others 1 (loadedRam SpinlockImage.image)
      (retryReadLocal devices) winProgram (winResume (.Ok none)) (wonLocal devices) := by
  rw [writer_program _ _ win_request]
  exact write_node Devices.bus others 1 (loadedRam SpinlockImage.image)
    (retryReadLocal devices) (SpinlockAccess.writeRequest .lock true 1#32) 1#32 winResume rfl rfl free

theorem second_work_step (n : Nat) (bound : n < 4) :
    fetchRun readFiveView 2000 (cycle false) (secondWork n) = some ((), secondWork (n + 1)) := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact second_work0
  · exact second_work1
  · exact second_work2
  · exact second_work3

theorem second_work_all (n : Nat) (bound : n ≤ 4) :
    cyclesRun readFiveView 2000 wonRegisters n = some (secondWork n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have earlier := ih (by omega)
    have next := second_work_step n (by omega)
    change (do
      let rs ← cyclesRun readFiveView 2000 wonRegisters n
      let (_, after) ← fetchRun readFiveView 2000 (cycle false) rs
      pure after) = _
    rw [earlier]
    change (fetchRun readFiveView 2000 (cycle false) (secondWork n) >>= fun (_, after) => some after) = _
    rw [next]
    rfl

theorem advance_increment (devices : Devices.State) (others : PhysicalAddress → Prop) :
    NodeSteps Devices.bus others 1 (loadedRam SpinlockImage.image)
      (winResume (.Ok none)) (wonLocal devices) incrementProgram (incrementLocal devices) := by
  let afterWin := { wonLocal devices with registers := wonRegisters }
  let afterWork := { wonLocal devices with registers := secondWork 4 }
  have finish := pauseRun_sound Devices.bus others 1 (loadedRam SpinlockImage.image) readFiveView 2000
    _ (wonLocal devices) (.pure ()) wonRegisters (Nat.le_refl 5) (fun _ => rfl) win_tail
  have work := cyclesRun_sound Devices.bus others 1 (loadedRam SpinlockImage.image) readFiveView 2000 4
    afterWin (secondWork 4) (Nat.le_refl 5) (fun _ => rfl) rfl (second_work_all 4 (by decide))
  have next := pauseRun_sound Devices.bus others 1 (loadedRam SpinlockImage.image) readFiveView 2000
    (cycle false) afterWork incrementProgram incrementRegisters (Nat.le_refl 5) (fun _ => rfl) increment_result
  have restart : NodeStep Devices.bus others 1 (loadedRam SpinlockImage.image)
      afterWork (.pure ()) (cycle false) afterWork := restart_step Devices.bus others _ _ afterWork false
  exact nodeSteps_trans finish (nodeSteps_trans work (.cons restart next))

theorem increment_commit (devices : Devices.State) (others : PhysicalAddress → Prop)
    (free : Disjoint (Footprint SpinlockImage.counterAddress 4) others) :
    NodeStep Devices.bus others 1 (loadedRam SpinlockImage.image)
      (incrementLocal devices) incrementProgram (incrementResume (.Ok none)) (incrementedLocal devices) := by
  rw [writer_program _ _ increment_request]
  exact write_node Devices.bus others 1 (loadedRam SpinlockImage.image)
    (incrementLocal devices) (SpinlockAccess.writeRequest .counter false 2#32) 2#32 incrementResume rfl rfl free

theorem advance_release (devices : Devices.State) (others : PhysicalAddress → Prop) :
    NodeSteps Devices.bus others 1 (loadedRam SpinlockImage.image)
      (incrementResume (.Ok none)) (incrementedLocal devices) releaseProgram (releaseLocal devices) := by
  let afterStore := { incrementedLocal devices with registers := incrementedRegisters }
  let atFence := { incrementedLocal devices with registers := secondFenceRegisters }
  let afterFence := { incrementedLocal devices with registers := secondFencedRegisters }
  have finishStore := pauseRun_sound Devices.bus others 1 (loadedRam SpinlockImage.image) readSixView 2000
    _ (incrementedLocal devices) (.pure ()) incrementedRegisters (show 5 ≤ 6 from by decide) (fun _ => rfl) increment_tail
  have restart1 : NodeStep Devices.bus others 1 (loadedRam SpinlockImage.image)
      afterStore (.pure ()) (cycle false) afterStore := restart_step Devices.bus others _ _ afterStore false
  have startFence := pauseRun_sound Devices.bus others 1 (loadedRam SpinlockImage.image) readSixView 2000
    (cycle false) afterStore secondFenceProgram secondFenceRegisters (show 5 ≤ 6 from by decide) (fun _ => rfl) second_fence_result
  have fenceStep : NodeStep Devices.bus others 1 (loadedRam SpinlockImage.image)
      atFence secondFenceProgram (secondFenceResume ()) atFence := by
    rw [barrier_program _ _ second_fence_kind]
    exact barrier_node Devices.bus others 1 (loadedRam SpinlockImage.image) atFence
      .Barrier_RISCV_rw_w secondFenceResume
  have finishFence := pauseRun_sound Devices.bus others 1 (loadedRam SpinlockImage.image) readSixView 2000
    _ atFence (.pure ()) secondFencedRegisters (show 5 ≤ 6 from by decide) (fun _ => rfl) second_fence_tail
  have restart2 : NodeStep Devices.bus others 1 (loadedRam SpinlockImage.image)
      afterFence (.pure ()) (cycle false) afterFence := restart_step Devices.bus others _ _ afterFence false
  have next := pauseRun_sound Devices.bus others 1 (loadedRam SpinlockImage.image) readSixView 2000
    (cycle false) afterFence releaseProgram releaseRegisters (show 5 ≤ 6 from by decide) (fun _ => rfl) release_result
  exact nodeSteps_trans finishStore (.cons restart1
    (nodeSteps_trans startFence (.cons fenceStep (nodeSteps_trans finishFence (.cons restart2 next)))))

theorem release_commit (devices : Devices.State) (others : PhysicalAddress → Prop)
    (free : Disjoint (Footprint SpinlockImage.lockAddress 4) others) :
    NodeStep Devices.bus others 1 (loadedRam SpinlockImage.image)
      (releaseLocal devices) releaseProgram (releaseResume (.Ok none)) (finalLocal devices) := by
  rw [writer_program _ _ release_request]
  exact write_node Devices.bus others 1 (loadedRam SpinlockImage.image)
    (releaseLocal devices) (SpinlockAccess.writeRequest .lock false 0#32) 0#32 releaseResume rfl rfl free

end MachCSL.Machine.SpinlockWitnessRelease
