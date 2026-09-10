import MachCSL.Machine.State
import MachCSL.Memory.ReservationProofs

/-! Hart-local log/view and global memory/reservation invariants. These
properties concern the existing node relation, with its explicit bus; they
introduce no new state invariant or pairwise reservation-disjointness premise. -/
namespace MachCSL.Machine
open Memory
open _root_.Sail.ConcurrencyInterfaceV1.Free

variable [Platform] (bus : Bus Device) (others : PhysicalAddress → Prop)
    (hart : Agent) (image : ByteMap 64)

/-- A hart node either preserves its log or publishes exactly one message. -/
theorem node_log_cases (s s' : LocalState Device) (m m' : SailM Unit)
    (step : NodeStep bus others hart image s m m' s') :
    s'.log = s.log ∨ ∃ message, s'.log = s.log ++ [message] := by
  cases m with
  | pure value =>
    obtain ⟨tick, _, rfl⟩ := step
    exact Or.inl rfl
  | impure event k =>
    cases event <;> simp only [NodeStep] at step
    all_goals first
      | solve | contradiction
      | solve | obtain ⟨_, rfl⟩ := step; exact Or.inl rfl
      | solve | obtain ⟨_, _, rfl⟩ := step; exact Or.inl rfl
      | skip
    case readMem n req =>
      split at step
      · obtain ⟨w, d, _, _, rfl⟩ := step
        exact Or.inl rfl
      · rcases step with ⟨_, view, w, _, _, _, _, rfl⟩ | ⟨_, blocked | acquired⟩
        · exact Or.inl rfl
        · obtain ⟨_, _, rfl⟩ := blocked
          exact Or.inl rfl
        · obtain ⟨_, w, _, _, rfl⟩ := acquired
          exact Or.inl rfl
    case writeMem n req =>
      split at step
      · contradiction
      · split at step
        · obtain ⟨d, _, _, rfl⟩ := step
          exact Or.inl rfl
        · rcases step with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨_, rfl⟩

theorem node_log_length_mono (s s' : LocalState Device) (m m' : SailM Unit)
    (step : NodeStep bus others hart image s m m' s') : s.log.length ≤ s'.log.length := by
  rcases node_log_cases bus others hart image s s' m m' step with h | ⟨message, h⟩
  · simp [h]
  · simp [h]

/-- A valid view never runs beyond the resulting log. -/
theorem node_view_bound (s s' : LocalState Device) (m m' : SailM Unit)
    (bound : s.view ≤ s.log.length)
    (step : NodeStep bus others hart image s m m' s') : s'.view ≤ s'.log.length := by
  cases m with
  | pure value =>
    obtain ⟨tick, _, rfl⟩ := step
    exact bound
  | impure event k =>
    cases event <;> simp only [NodeStep] at step
    all_goals first
      | solve | contradiction
      | solve | obtain ⟨_, rfl⟩ := step; exact bound
      | solve | obtain ⟨_, _, rfl⟩ := step; exact bound
      | skip
    case readMem n req =>
      split at step
      · obtain ⟨w, d, _, _, rfl⟩ := step
        exact bound
      · rcases step with ⟨_, view, w, _, upper, _, _, rfl⟩ | ⟨_, blocked | acquired⟩
        · exact upper
        · obtain ⟨_, _, rfl⟩ := blocked
          exact bound
        · obtain ⟨_, w, _, _, rfl⟩ := acquired
          exact Nat.le_refl _
    case writeMem n req =>
      split at step
      · contradiction
      · split at step
        · obtain ⟨d, _, _, rfl⟩ := step
          exact bound
        · rcases step with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
          · exact bound
          · dsimp
            split <;> simp only [List.length_append, List.length_singleton] <;> omega
    case barrier b =>
      obtain ⟨_, rfl⟩ := step
      exact fencePost_le_length hart s.log (fenceDrains b) s.view bound

/-- All three source `mm_ok` conjuncts survive a concrete hart step. -/
theorem hart_memory_ok (g g' : State) (cpu : CPU) (m m' : SailM Unit)
    (initial : MemoryOK g) (step : HartStep g cpu m m' g') : MemoryOK g' := by
  obtain ⟨after, step, rfl⟩ := step
  refine ⟨?_, ?_, ?_⟩
  · exact node_flat_preserved Devices.bus _ _ g.image (focus g cpu) after m m' initial.1 step
  · intro other
    by_cases he : other = cpu
    · subst other
      simp only [writeBack, updateHart, ↓reduceIte]
      exact node_view_bound Devices.bus _ _ g.image (focus g cpu) after m m' (initial.2.1 cpu) step
    · simp only [writeBack, updateHart, he, ↓reduceIte]
      exact Nat.le_trans (initial.2.1 other)
        (node_log_length_mono Devices.bus _ _ g.image (focus g cpu) after m m' step)
  · exact initial.2.2

/-- A hart's surviving reservation still agrees with the post-state memory. -/
theorem node_self_reservation (s s' : LocalState Device) (m m' : SailM Unit)
    (initial : ∀ reserved, s.reservation = some reserved → Submap reserved s.memory)
    (step : NodeStep bus others hart image s m m' s') :
    ∀ reserved, s'.reservation = some reserved → Submap reserved s'.memory := by
  intro reserved present
  cases m with
  | pure value =>
    obtain ⟨tick, _, rfl⟩ := step
    contradiction
  | impure event k =>
    cases event <;> simp only [NodeStep] at step
    all_goals first
      | solve | contradiction
      | solve | obtain ⟨_, rfl⟩ := step; exact initial reserved present
      | solve | obtain ⟨_, _, rfl⟩ := step; exact initial reserved present
      | skip
    case readMem n req =>
      split at step
      · obtain ⟨w, d, _, _, rfl⟩ := step
        exact initial reserved present
      · rcases step with ⟨_, view, w, _, _, _, _, rfl⟩ | ⟨_, blocked | acquired⟩
        · exact initial reserved present
        · obtain ⟨_, _, rfl⟩ := blocked
          contradiction
        · obtain ⟨_, w, reads, _, rfl⟩ := acquired
          cases present
          exact snapshot_submap s.memory req.pa n w reads
    case writeMem n req =>
      split at step
      · contradiction
      · split at step
        · obtain ⟨d, _, _, rfl⟩ := step
          contradiction
        · rcases step with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
          · exact initial reserved present
          · contradiction

/-- Any other hart's reserved bytes are preserved because a completed write
must be disjoint from the supplied union of other reservations. -/
theorem node_preserves_reserved_memory (s s' : LocalState Device) (m m' : SailM Unit)
    (reserved : ByteMap 64) (initial : Submap reserved s.memory)
    (included : ∀ address, Domain reserved address → others address)
    (step : NodeStep bus others hart image s m m' s') : Submap reserved s'.memory := by
  cases m with
  | pure value =>
    obtain ⟨tick, _, rfl⟩ := step
    exact initial
  | impure event k =>
    cases event <;> simp only [NodeStep] at step
    all_goals first
      | solve | contradiction
      | solve | obtain ⟨_, rfl⟩ := step; exact initial
      | solve | obtain ⟨_, _, rfl⟩ := step; exact initial
      | skip
    case readMem n req =>
      split at step
      · obtain ⟨w, d, _, _, rfl⟩ := step
        exact initial
      · rcases step with ⟨_, view, w, _, _, _, _, rfl⟩ | ⟨_, blocked | acquired⟩
        · exact initial
        · obtain ⟨_, _, rfl⟩ := blocked
          exact initial
        · obtain ⟨_, w, _, _, rfl⟩ := acquired
          exact initial
    case writeMem n req =>
      split at step
      · contradiction
      · rename_i value hv
        split at step
        · obtain ⟨d, _, _, rfl⟩ := step
          exact initial
        · rcases step with ⟨_, _, rfl⟩ | ⟨disjoint, _, rfl⟩
          · exact initial
          · apply writeBytes_preserves_submap s.memory reserved req.pa n value initial
            intro address footprint reservedByte
            exact disjoint address footprint (included address reservedByte)

/-- Full source `resv_ok` preservation, without a pairwise-disjointness premise. -/
theorem hart_reservations_ok (g g' : State) (cpu : CPU) (m m' : SailM Unit)
    (initial : ReservationsOK g) (step : HartStep g cpu m m' g') : ReservationsOK g' := by
  obtain ⟨after, step, rfl⟩ := step
  intro other reserved present
  by_cases he : other = cpu
  · subst other
    have hp : after.reservation = some reserved := by
      simpa only [writeBack, updateHart, ↓reduceIte] using present
    exact node_self_reservation Devices.bus _ _ g.image (focus g cpu) after m m'
      (initial cpu) step reserved hp
  · have hp : g.reservations other = some reserved := by
      simpa only [writeBack, updateHart, he, ↓reduceIte] using present
    apply node_preserves_reserved_memory Devices.bus (othersReserved g.reservations cpu)
      (hartAgent cpu) g.image (focus g cpu) after m m' reserved (initial other reserved hp) _ step
    intro address hdomain
    exact ⟨other, he, reserved, hp, hdomain⟩

end MachCSL.Machine
