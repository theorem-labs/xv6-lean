import Xv6.Kernel.MycpuKptWitnessCompactProofs

namespace Xv6.Kernel.MycpuKptWitness
open MachCSL MachCSL.Machine MachCSL.Memory
attribute [local instance] platform
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

/-- Actual generated cycle 8. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_7 : run cachedImage cpu 4 (cycle false) (stateAt 7) = some (stateAt 8) := by
  rw [← compact_state_eq ⟨7, by decide⟩, ← compact_state_eq ⟨8, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

/-- Actual generated cycle 9. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_8 : run cachedImage cpu 4 (cycle false) (stateAt 8) = some (stateAt 9) := by
  rw [← compact_state_eq ⟨8, by decide⟩, ← compact_state_eq ⟨9, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

/-- Actual generated cycle 10. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_9 : run cachedImage cpu 4 (cycle false) (stateAt 9) = some (stateAt 10) := by
  rw [← compact_state_eq ⟨9, by decide⟩, ← compact_state_eq ⟨10, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

/-- Actual generated cycle 11. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_10 : run cachedImage cpu 4 (cycle false) (stateAt 10) = some (stateAt 11) := by
  rw [← compact_state_eq ⟨10, by decide⟩, ← compact_state_eq ⟨11, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

/-- Actual generated cycle 12. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_11 : run cachedImage cpu 4 (cycle false) (stateAt 11) = some (stateAt 12) := by
  rw [← compact_state_eq ⟨11, by decide⟩, ← compact_state_eq ⟨12, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

/-- Actual generated cycle 13. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_12 : run cachedImage cpu 4 (cycle false) (stateAt 12) = some (stateAt 13) := by
  rw [← compact_state_eq ⟨12, by decide⟩, ← compact_state_eq ⟨13, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

/-- Actual generated cycle 14. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_13 : run cachedImage cpu 4 (cycle false) (stateAt 13) = some (stateAt 14) := by
  rw [← compact_state_eq ⟨13, by decide⟩, ← compact_state_eq ⟨14, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

end Xv6.Kernel.MycpuKptWitness
