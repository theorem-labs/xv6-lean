import MachCSL.Machine.SpinlockWitnessHeldState
import MachCSL.Machine.SpinlockWitnessHeldRun
import MachCSL.Machine.SpinlockWitnessHeldCertificates

namespace MachCSL.Machine.SpinlockWitnessHeld
open MachCSL.Memory MachCSL.Machine.SpinlockWitness
attribute [local instance] SpinlockWitness.platform
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def startingLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (pausedRegisters 0) (loadedRam SpinlockImage.image) [] 0 (some zeroSnapshot) devices

def waitingLocal (devices : Devices.State) : LocalState Devices.State :=
  localAt (pausedRegisters 1) memoryTwo logTwo 0 none devices

theorem work_step (n : Nat) (bound : n < 4) :
    fetchRun readOne 2000 (cycle false) (workAfter n) = some ((), workAfter (n + 1)) := by
  have cases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact work0
  · exact work1
  · exact work2
  · exact work3

theorem work_all (n : Nat) (bound : n ≤ 4) :
    cyclesRun readOne 2000 acquiredRegisters n = some (workAfter n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have earlier := ih (by omega)
    have next := work_step n (by omega)
    change (do
      let rs ← cyclesRun readOne 2000 acquiredRegisters n
      let (_, after) ← fetchRun readOne 2000 (cycle false) rs
      pure after) = _
    rw [earlier]
    change (fetchRun readOne 2000 (cycle false) (workAfter n) >>= fun (_, after) => some after) = _
    rw [next]
    rfl

theorem work_run : cyclesRun readOne 2000 acquiredRegisters 4 = some (workAfter 4) :=
  work_all 4 (by decide)

theorem swap_prefix_zero (devices : Devices.State) (others : PhysicalAddress → Prop) :
    NodeSteps Devices.bus others 0 (loadedRam SpinlockImage.image)
      ((readBoundary 0).2 (.Ok (0#32, none))) (startingLocal devices)
      (swapProgram 0 0#32) (startingLocal devices) := by
  exact pauseRun_sound Devices.bus others 0 (loadedRam SpinlockImage.image)
    (loadedRam SpinlockImage.image) 2000 _ (startingLocal devices) _ (pausedRegisters 0)
    (Nat.le_refl 0) (fun _ => rfl) (swap0_result _)

theorem swap_commit (devices : Devices.State) (others : PhysicalAddress → Prop)
    (free : Disjoint (Footprint SpinlockImage.lockAddress 4) others) :
    NodeStep Devices.bus others 0 (loadedRam SpinlockImage.image)
      (startingLocal devices) (swapProgram 0 0#32) (swapResume 0 0#32 (.Ok none)) (swapLocal devices) := by
  rw [writer_program _ _ swap0_request]
  exact write_node Devices.bus others 0 (loadedRam SpinlockImage.image)
    (startingLocal devices) (SpinlockAccess.writeRequest .lock true 1#32) 1#32
    (swapResume 0 0#32) rfl rfl free

theorem advance_counter (devices : Devices.State) (others : PhysicalAddress → Prop) :
    NodeSteps Devices.bus others 0 (loadedRam SpinlockImage.image)
      (swapResume 0 0#32 (.Ok none)) (swapLocal devices) counterProgram (counterLocal devices) := by
  let afterSwap := { swapLocal devices with registers := acquiredRegisters }
  let afterWork := { swapLocal devices with registers := workAfter 4 }
  have finish := pauseRun_sound Devices.bus others 0 (loadedRam SpinlockImage.image) readOne 2000
    _ (swapLocal devices) (.pure ()) acquiredRegisters (Nat.le_refl 1) (fun _ => rfl) swap_tail
  have work := cyclesRun_sound Devices.bus others 0 (loadedRam SpinlockImage.image) readOne 2000 4
    afterSwap (workAfter 4) (Nat.le_refl 1) (fun _ => rfl) rfl work_run
  have next := pauseRun_sound Devices.bus others 0 (loadedRam SpinlockImage.image) readOne 2000
    (cycle false) afterWork counterProgram counterRegisters (Nat.le_refl 1) (fun _ => rfl) counter_result
  have restart : NodeStep Devices.bus others 0 (loadedRam SpinlockImage.image)
      afterWork (.pure ()) (cycle false) afterWork := restart_step Devices.bus others _ _ afterWork false
  exact nodeSteps_trans finish (nodeSteps_trans work (.cons restart next))

theorem counter_commit (devices : Devices.State) (others : PhysicalAddress → Prop)
    (free : Disjoint (Footprint SpinlockImage.counterAddress 4) others) :
    NodeStep Devices.bus others 0 (loadedRam SpinlockImage.image)
      (counterLocal devices) counterProgram (counterResume (.Ok none)) (committedLocal devices) := by
  rw [writer_program _ _ counter_request]
  exact write_node Devices.bus others 0 (loadedRam SpinlockImage.image)
    (counterLocal devices) (SpinlockAccess.writeRequest .counter false 1#32) 1#32
    counterResume rfl rfl free

theorem read_one (devices : Devices.State) (others : PhysicalAddress → Prop)
    (free : Disjoint (Footprint SpinlockImage.lockAddress 4) others) :
    NodeStep Devices.bus others 1 (loadedRam SpinlockImage.image)
      (waitingLocal devices) (paused 1).1 ((readBoundary 1).2 (.Ok (1#32, none))) (readerLocal devices) := by
  rw [paused_program 1]
  exact read_exclusive_node Devices.bus others 1 (loadedRam SpinlockImage.image)
    (waitingLocal devices) (SpinlockAccess.readRequest .lock true) 1#32 (readBoundary 1).2
    rfl rfl free memoryTwo_lock

theorem swap_prefix_one (devices : Devices.State) (others : PhysicalAddress → Prop) :
    NodeSteps Devices.bus others 1 (loadedRam SpinlockImage.image)
      ((readBoundary 1).2 (.Ok (1#32, none))) (readerLocal devices)
      (swapProgram 1 1#32) (readerLocal devices) := by
  exact pauseRun_sound Devices.bus others 1 (loadedRam SpinlockImage.image)
    (read (loadedRam SpinlockImage.image) logTwo 1 2) 2000 _ (readerLocal devices) _ (pausedRegisters 1)
    (Nat.le_refl 2) (fun _ => rfl) (swap1_result _)

theorem advance_unlock (devices : Devices.State) (others : PhysicalAddress → Prop) :
    NodeSteps Devices.bus others 0 (loadedRam SpinlockImage.image)
      (counterResume (.Ok none)) (committedLocal devices) unlockProgram (unlockLocal devices) := by
  let afterStore := { committedLocal devices with registers := storedRegisters }
  let atFence := { committedLocal devices with registers := fenceRegisters }
  let afterFence := { committedLocal devices with registers := fencedRegisters }
  have finishStore := pauseRun_sound Devices.bus others 0 (loadedRam SpinlockImage.image) readTwo 2000
    _ (committedLocal devices) (.pure ()) storedRegisters (show 1 ≤ 2 from by decide) (fun _ => rfl) counter_tail
  have restart1 : NodeStep Devices.bus others 0 (loadedRam SpinlockImage.image)
      afterStore (.pure ()) (cycle false) afterStore := restart_step Devices.bus others _ _ afterStore false
  have startFence := pauseRun_sound Devices.bus others 0 (loadedRam SpinlockImage.image) readTwo 2000
    (cycle false) afterStore fenceProgram fenceRegisters (show 1 ≤ 2 from by decide) (fun _ => rfl) fence_result
  have fenceStep : NodeStep Devices.bus others 0 (loadedRam SpinlockImage.image)
      atFence fenceProgram (fenceResume ()) atFence := by
    rw [barrier_program _ _ fence_kind]
    exact barrier_node Devices.bus others 0 (loadedRam SpinlockImage.image) atFence
      .Barrier_RISCV_rw_w fenceResume
  have finishFence := pauseRun_sound Devices.bus others 0 (loadedRam SpinlockImage.image) readTwo 2000
    _ atFence (.pure ()) fencedRegisters (show 1 ≤ 2 from by decide) (fun _ => rfl) fence_tail
  have restart2 : NodeStep Devices.bus others 0 (loadedRam SpinlockImage.image)
      afterFence (.pure ()) (cycle false) afterFence := restart_step Devices.bus others _ _ afterFence false
  have next := pauseRun_sound Devices.bus others 0 (loadedRam SpinlockImage.image) readTwo 2000
    (cycle false) afterFence unlockProgram unlockRegisters (show 1 ≤ 2 from by decide) (fun _ => rfl) unlock_result
  exact nodeSteps_trans finishStore (.cons restart1
    (nodeSteps_trans startFence (.cons fenceStep (nodeSteps_trans finishFence (.cons restart2 next)))))

theorem unlock_blocked (devices : Devices.State) (others : PhysicalAddress → Prop)
    (blocked : ¬ Disjoint (Footprint SpinlockImage.lockAddress 4) others) :
    NodeStep Devices.bus others 0 (loadedRam SpinlockImage.image)
      (unlockLocal devices) unlockProgram unlockProgram (unlockLocal devices) := by
  rw [writer_program _ _ unlock_request]
  exact blocked_write_node Devices.bus others 0 (loadedRam SpinlockImage.image)
    (unlockLocal devices) (SpinlockAccess.writeRequest .lock false 0#32) 0#32 unlockResume rfl rfl blocked

end MachCSL.Machine.SpinlockWitnessHeld
