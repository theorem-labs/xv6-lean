import MachCSL.Machine.Node

namespace MachCSL.Machine
open Memory
open _root_.Sail.ConcurrencyInterfaceV1.Free

variable [Platform] (bus : Bus Device) (others : PhysicalAddress → Prop)
    (hart : Agent) (image : ByteMap 64)

/-- Every hart event keeps the materialized memory equal to the TSO log.
The MMIO bus can change device state but cannot alter RAM. -/
theorem node_flat_preserved (s s' : LocalState Device) (m m' : SailM Unit)
    (initial : s.memory = flat image s.log)
    (step : NodeStep bus others hart image s m m' s') :
    s'.memory = flat image s'.log := by
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
        · rcases step with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
          · exact initial
          · exact (flat_writeBytes image s.log req.pa n value hart).symm ▸
              congrArg (fun mm => writeBytes mm req.pa n value) initial

/-- View advancement is monotone for every possible hart node. -/
theorem node_view_monotone (s s' : LocalState Device) (m m' : SailM Unit)
    (bound : s.view ≤ s.log.length)
    (step : NodeStep bus others hart image s m m' s') : s.view ≤ s'.view := by
  cases m with
  | pure value =>
    obtain ⟨tick, _, rfl⟩ := step
    exact Nat.le_refl _
  | impure event k =>
    cases event <;> simp only [NodeStep] at step
    all_goals first
      | solve | contradiction
      | solve | obtain ⟨_, rfl⟩ := step; exact Nat.le_refl _
      | solve | obtain ⟨_, _, rfl⟩ := step; exact Nat.le_refl _
      | skip
    case readMem n req =>
      split at step
      · obtain ⟨w, d, _, _, rfl⟩ := step
        exact Nat.le_refl _
      · rcases step with ⟨_, view, w, advance, _, _, _, rfl⟩ | ⟨_, blocked | acquired⟩
        · exact advance
        · obtain ⟨_, _, rfl⟩ := blocked
          exact Nat.le_refl _
        · obtain ⟨_, w, _, _, rfl⟩ := acquired
          exact bound
    case writeMem n req =>
      split at step
      · contradiction
      · split at step
        · obtain ⟨d, _, _, rfl⟩ := step
          exact Nat.le_refl _
        · rcases step with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
          · exact Nat.le_refl _
          · dsimp
            split <;> omega
    case barrier b =>
      obtain ⟨_, rfl⟩ := step
      exact fencePost_mono hart s.log (fenceDrains b) s.view

end MachCSL.Machine
