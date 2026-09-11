import MachCSL.Machine.SpinlockWitnessHeldLocal

namespace MachCSL.Machine.SpinlockWitnessHeld
open MachCSL.Memory MachCSL.Machine.SpinlockWitness

theorem starting_focus (before : State) :
    focus (afterReadZero before) 0 = startingLocal (Devices.reset before.devices) := by
  simp only [afterReadZero, reservedLocal, bothPaused, firstPaused,
    focus, writeBack, updateHart_other _ _ _ _ (show (0 : CPU) ≠ 1 from by decide),
    updateHart_same, pausedLocal, bootLocal, paused, startingLocal, localAt]

theorem swapped_focus (before : State) :
    focus (swapped before) 0 = swapLocal (Devices.reset before.devices) := focus_writeBack _ _ _

theorem counter_focus (before : State) :
    focus (counterReady before) 0 = counterLocal (Devices.reset before.devices) := focus_writeBack _ _ _

theorem committed_focus (before : State) :
    focus (counterCommitted before) 0 = committedLocal (Devices.reset before.devices) := focus_writeBack _ _ _

theorem waiting_focus (before : State) :
    focus (counterCommitted before) 1 = waitingLocal (Devices.reset before.devices) := by
  simp only [counterCommitted, counterReady, swapped, afterReadZero, bothPaused,
    focus, writeBack, updateHart_other _ _ _ _ (show (1 : CPU) ≠ 0 from by decide),
    updateHart_same, committedLocal, localAt, waitingLocal, pausedLocal, bootLocal, paused]

theorem reader_focus (before : State) :
    focus (oneReserved before) 1 = readerLocal (Devices.reset before.devices) := focus_writeBack _ _ _

theorem committed_other_focus (before : State) :
    focus (oneReserved before) 0 = committedLocal (Devices.reset before.devices) := by
  simp only [oneReserved, counterCommitted, focus, writeBack,
    updateHart_other _ _ _ _ (show (0 : CPU) ≠ 1 from by decide), updateHart_same,
    readerLocal, committedLocal, localAt]

theorem unlock_focus (before : State) :
    focus (unlockReady before) 0 = unlockLocal (Devices.reset before.devices) := focus_writeBack _ _ _

theorem reader_other_focus (before : State) :
    focus (unlockReady before) 1 = readerLocal (Devices.reset before.devices) := by
  simp only [unlockReady, oneReserved, focus, writeBack,
    updateHart_other _ _ _ _ (show (1 : CPU) ≠ 0 from by decide), updateHart_same,
    unlockLocal, readerLocal, localAt]

theorem swapped_reservations (before : State) (cpu : CPU) :
    (swapped before).reservations cpu = none := by
  change updateHart (afterReadZero before).reservations 0 none cpu = none
  rw [afterReadZero_reservations, updateHart_twice]
  simp [updateHart]

theorem counter_reservations (before : State) (cpu : CPU) :
    (counterReady before).reservations cpu = none := by
  change updateHart (swapped before).reservations 0 none cpu = none
  by_cases same : cpu = 0
  · simp [updateHart, same]
  · rw [updateHart_other _ _ _ _ same]
    exact swapped_reservations before cpu

theorem committed_reservations (before : State) (cpu : CPU) :
    (counterCommitted before).reservations cpu = none := by
  change updateHart (counterReady before).reservations 0 none cpu = none
  by_cases same : cpu = 0
  · simp [updateHart, same]
  · rw [updateHart_other _ _ _ _ same]
    exact counter_reservations before cpu

theorem no_others (reservations : CPU → Option Reservation) (cpu : CPU)
    (empty : ∀ other, reservations other = none) (address : PhysicalAddress) :
    ¬ othersReserved reservations cpu address := by
  rintro ⟨other, _, snapshot, found, _⟩
  rw [empty] at found
  contradiction

theorem swap_free (before : State) :
    Disjoint (Footprint SpinlockImage.lockAddress 4) (othersReserved (afterReadZero before).reservations 0) := by
  intro address _ reserved
  rcases reserved with ⟨cpu, other, snapshot, found, _⟩
  rw [afterReadZero_reservations] at found
  simp [updateHart, other] at found

theorem counter_free (before : State) :
    Disjoint (Footprint SpinlockImage.counterAddress 4) (othersReserved (counterReady before).reservations 0) := by
  intro address _ reserved
  exact no_others _ 0 (counter_reservations before) address reserved

theorem reader_free (before : State) :
    Disjoint (Footprint SpinlockImage.lockAddress 4) (othersReserved (counterCommitted before).reservations 1) := by
  intro address _ reserved
  exact no_others _ 1 (committed_reservations before) address reserved

theorem one_reserved (before : State) :
    (oneReserved before).reservations 1 = some oneSnapshot := by
  simp only [oneReserved, writeBack, readerLocal, localAt, updateHart_same]

theorem unlock_one_reserved (before : State) :
    (unlockReady before).reservations 1 = some oneSnapshot := by
  simp only [unlockReady, writeBack, unlockLocal, localAt,
    updateHart_other _ _ _ _ (show (1 : CPU) ≠ 0 from by decide)]
  exact one_reserved before

theorem unlock_zero_clear (before : State) :
    (unlockReady before).reservations 0 = none := by
  simp only [unlockReady, writeBack, unlockLocal, localAt, updateHart_same]

theorem unlock_conflict (before : State) :
    ¬ Disjoint (Footprint SpinlockImage.lockAddress 4) (othersReserved (unlockReady before).reservations 0) := by
  intro disjoint
  apply disjoint SpinlockImage.lockAddress
  · exact ⟨0, by decide, rfl⟩
  · exact ⟨1, by decide, oneSnapshot, unlock_one_reserved before, 1#8, rfl⟩

theorem unlock_values (before : State) :
    readBytes (unlockReady before).memory SpinlockImage.lockAddress 4 = some 1#32 ∧
    readBytes (unlockReady before).memory SpinlockImage.counterAddress 4 = some 1#32 :=
  ⟨memoryTwo_lock, memoryTwo_counter⟩

theorem unlock_log (before : State) :
    (unlockReady before).log = [lockMessage, counterMessage] := rfl

theorem unlock_disk (before : State) :
    (unlockReady before).devices.virtio.v_disk = before.devices.virtio.v_disk := rfl

theorem blocked_pool_length (generation : Nat) : (blockedPool generation).length = 12 := by
  simp [blockedPool, pairPool, tailWorkers, powerFork_length]

end MachCSL.Machine.SpinlockWitnessHeld
