import Xv6.Kernel.MycpuKptWitnessCompactProofs

namespace Xv6.Kernel.MycpuKptWitness
open MachCSL MachCSL.Machine MachCSL.Memory
attribute [local instance] platform
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

/-- Actual generated cycle 1. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_0 : run cachedImage cpu 4 (cycle false) (stateAt 0) = some (stateAt 1) := by
  rw [← compact_state_eq ⟨0, by decide⟩, ← compact_state_eq ⟨1, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

/-- Actual generated cycle 2. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_1 : run cachedImage cpu 4 (cycle false) (stateAt 1) = some (stateAt 2) := by
  rw [← compact_state_eq ⟨1, by decide⟩, ← compact_state_eq ⟨2, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

/-- Actual generated cycle 3. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_2 : run cachedImage cpu 4 (cycle false) (stateAt 2) = some (stateAt 3) := by
  rw [← compact_state_eq ⟨2, by decide⟩, ← compact_state_eq ⟨3, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

/-- Actual generated cycle 4. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_3 : run cachedImage cpu 4 (cycle false) (stateAt 3) = some (stateAt 4) := by
  rw [← compact_state_eq ⟨3, by decide⟩, ← compact_state_eq ⟨4, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

/-- Actual generated cycle 5. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_4 : run cachedImage cpu 4 (cycle false) (stateAt 4) = some (stateAt 5) := by
  rw [← compact_state_eq ⟨4, by decide⟩, ← compact_state_eq ⟨5, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

/-- Actual generated cycle 6. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_5 : run cachedImage cpu 4 (cycle false) (stateAt 5) = some (stateAt 6) := by
  rw [← compact_state_eq ⟨5, by decide⟩, ← compact_state_eq ⟨6, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

/-- Actual generated cycle 7. The compact input/output are first related
to the original entire checkpoints; every actual register and state field is checked. -/
theorem cycle_6 : run cachedImage cpu 4 (cycle false) (stateAt 6) = some (stateAt 7) := by
  rw [← compact_state_eq ⟨6, by decide⟩, ← compact_state_eq ⟨7, by decide⟩]
  with_unfolding_all change some _ = some _
  apply congrArg some
  with_unfolding_all change LocalState.mk _ _ _ _ _ _ = LocalState.mk _ _ _ _ _ _
  rw [LocalState.mk.injEq]
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  funext r
  cases r <;> rfl

end Xv6.Kernel.MycpuKptWitness
