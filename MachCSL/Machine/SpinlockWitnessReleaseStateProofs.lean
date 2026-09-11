import MachCSL.Machine.SpinlockWitnessReleaseLocal

namespace MachCSL.Machine.SpinlockWitnessRelease
open MachCSL.Memory MachCSL.Machine.SpinlockWitness MachCSL.Machine.SpinlockWitnessHeld

theorem failed_focus (before : State) :
    focus (failedState before) 1 = failedLocal (Devices.reset before.devices) := focus_writeBack _ _ _

theorem first_release_focus (before : State) :
    focus (failedState before) 0 = firstReleaseLocal (Devices.reset before.devices) := by
  simp only [failedState, unlockReady, focus, writeBack,
    updateHart_other _ _ _ _ (show (0 : CPU) ≠ 1 from by decide), updateHart_same,
    failedLocal, unlockLocal, firstReleaseLocal, localAt]

theorem retry_start_focus (before : State) :
    focus (releasedState before) 1 = retryStartLocal (Devices.reset before.devices) := by
  simp only [releasedState, failedState, focus, writeBack,
    updateHart_other _ _ _ _ (show (1 : CPU) ≠ 0 from by decide), updateHart_same,
    releasedLocal, failedLocal, retryStartLocal, localAt]

theorem retry_focus (before : State) :
    focus (retryState before) 1 = retryLocal (Devices.reset before.devices) := focus_writeBack _ _ _
theorem retry_read_focus (before : State) :
    focus (retryReadState before) 1 = retryReadLocal (Devices.reset before.devices) := focus_writeBack _ _ _
theorem won_focus (before : State) :
    focus (wonState before) 1 = wonLocal (Devices.reset before.devices) := focus_writeBack _ _ _
theorem increment_focus (before : State) :
    focus (incrementState before) 1 = incrementLocal (Devices.reset before.devices) := focus_writeBack _ _ _
theorem incremented_focus (before : State) :
    focus (incrementedState before) 1 = incrementedLocal (Devices.reset before.devices) := focus_writeBack _ _ _
theorem release_focus (before : State) :
    focus (releaseState before) 1 = releaseLocal (Devices.reset before.devices) := focus_writeBack _ _ _

theorem unlock_reservations (before : State) :
    (unlockReady before).reservations = updateHart (fun _ => none) 1 (some oneSnapshot) := by
  funext cpu
  by_cases zero : cpu = 0
  · subst cpu
    rw [unlock_zero_clear, updateHart_other _ _ _ _ (show (0 : CPU) ≠ 1 from by decide)]
  · by_cases one : cpu = 1
    · subst cpu
      rw [unlock_one_reserved, updateHart_same]
    · simp only [unlockReady, oneReserved, writeBack, unlockLocal, readerLocal, localAt,
        updateHart_other _ _ _ _ zero, updateHart_other _ _ _ _ one]
      exact committed_reservations before cpu

theorem failed_free (before : State) :
    Disjoint (Footprint SpinlockImage.lockAddress 4) (othersReserved (unlockReady before).reservations 1) := by
  intro address _ reserved
  rcases reserved with ⟨cpu, other, snapshot, found, _⟩
  rw [unlock_reservations, updateHart_other _ _ _ _ other] at found
  contradiction

theorem failed_reservations (before : State) (cpu : CPU) :
    (failedState before).reservations cpu = none := by
  simp only [failedState, writeBack, failedLocal, localAt]
  rw [unlock_reservations, updateHart_twice]
  simp [updateHart]

theorem writeBack_empty (g : State) (cpu : CPU) (s : LocalState Devices.State)
    (clear : s.reservation = none) (empty : ∀ cpu, g.reservations cpu = none) :
    ∀ other, (writeBack g cpu s).reservations other = none := by
  intro other
  simp only [writeBack, clear]
  by_cases same : other = cpu
  · subst other
    exact updateHart_same _ _ _
  · rw [updateHart_other _ _ _ _ same]
    exact empty other

theorem released_reservations (before : State) :
    ∀ cpu, (releasedState before).reservations cpu = none :=
  writeBack_empty (failedState before) 0 (releasedLocal (Devices.reset before.devices)) rfl (failed_reservations before)
theorem retry_reservations (before : State) :
    ∀ cpu, (retryState before).reservations cpu = none :=
  writeBack_empty (releasedState before) 1 (retryLocal (Devices.reset before.devices)) rfl (released_reservations before)
theorem overwrite_empty (g : State) (cpu : CPU) (first last : LocalState Devices.State)
    (clear : last.reservation = none) (empty : ∀ cpu, g.reservations cpu = none) :
    ∀ other, (writeBack (writeBack g cpu first) cpu last).reservations other = none := by
  intro other
  simp only [writeBack, clear, updateHart_twice]
  by_cases same : other = cpu
  · subst other
    exact updateHart_same _ _ _
  · rw [updateHart_other _ _ _ _ same]
    exact empty other

theorem won_reservations (before : State) :
    ∀ cpu, (wonState before).reservations cpu = none :=
  overwrite_empty (retryState before) 1
    (retryReadLocal (Devices.reset before.devices)) (wonLocal (Devices.reset before.devices))
    rfl (retry_reservations before)

theorem increment_reservations (before : State) :
    ∀ cpu, (incrementState before).reservations cpu = none :=
  writeBack_empty (wonState before) 1 (incrementLocal (Devices.reset before.devices)) rfl (won_reservations before)
theorem incremented_reservations (before : State) :
    ∀ cpu, (incrementedState before).reservations cpu = none :=
  writeBack_empty (incrementState before) 1 (incrementedLocal (Devices.reset before.devices)) rfl (increment_reservations before)
theorem release_reservations (before : State) :
    ∀ cpu, (releaseState before).reservations cpu = none :=
  writeBack_empty (incrementedState before) 1 (releaseLocal (Devices.reset before.devices)) rfl (incremented_reservations before)
theorem final_reservations (before : State) :
    ∀ cpu, (finalState before).reservations cpu = none :=
  writeBack_empty (releaseState before) 1 (finalLocal (Devices.reset before.devices)) rfl (release_reservations before)

theorem clear_free (g : State) (cpu : CPU) (address : PhysicalAddress) (n : Nat)
    (empty : ∀ other, g.reservations other = none) :
    Disjoint (Footprint address n) (othersReserved g.reservations cpu) := by
  intro byte _ reserved
  exact no_others _ cpu empty byte reserved

theorem win_free (before : State) :
    Disjoint (Footprint SpinlockImage.lockAddress 4) (othersReserved (retryReadState before).reservations 1) := by
  simp only [retryReadState, othersReserved_writeBack]
  exact clear_free _ _ _ _ (retry_reservations before)

theorem final_values (before : State) :
    readBytes (finalState before).memory SpinlockImage.lockAddress 4 = some 0#32 ∧
    readBytes (finalState before).memory SpinlockImage.counterAddress 4 = some 2#32 :=
  ⟨memorySeven_lock, memorySeven_counter⟩

theorem final_log (before : State) :
    (finalState before).log = [lockMessage, counterMessage, failedMessage, releaseZeroMessage,
      winMessage, incrementMessage, releaseOneMessage] := rfl

theorem final_log_authors (before : State) :
    (finalState before).log.map Message.author = [0, 0, 1, 0, 1, 1, 1] := rfl

theorem final_disk (before : State) :
    (finalState before).devices.virtio.v_disk = before.devices.virtio.v_disk := rfl

theorem final_pool_length (generation : Nat) : (finalPool generation).length = 12 := by
  simp [finalPool, pairPool, tailWorkers, powerFork_length]

theorem final_generation (before : State) :
    (finalState before).generation = before.generation ∧ (finalState before).power = true := ⟨rfl, rfl⟩

theorem final_other_registers (before : State) (cpu : CPU) (zero : cpu ≠ 0) (one : cpu ≠ 1) :
    (finalState before).registers cpu = (bootState SpinlockImage.image before).registers cpu := by
  simp only [finalState, releaseState, incrementedState, incrementState, wonState, retryReadState,
    retryState, releasedState, failedState, unlockReady, oneReserved, counterCommitted,
    counterReady, swapped, writeBack, updateHart_other _ _ _ _ zero, updateHart_other _ _ _ _ one]
  exact conflict_other_registers before cpu zero one

end MachCSL.Machine.SpinlockWitnessRelease
