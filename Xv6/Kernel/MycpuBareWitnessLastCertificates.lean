import Xv6.Kernel.MycpuBareWitnessOrderProofs

namespace Xv6.Kernel.MycpuBareWitness
open MachCSL MachCSL.Machine MachCSL.Logic
attribute [local instance] platform
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- Complete generated cycle 8: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_7 : run 4 (cycle false) (stateAt 7) = some (stateAt 8) := by
  have generated : run 4 (cycle false) (stateAt 7) = some { stateAt 8 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 7 (checkpoint 7)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 7 (checkpoint 7)) =
      checkpoint 8 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 7 r member).symm
  rw [registers] at generated
  exact generated

/-- Complete generated cycle 9: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_8 : run 4 (cycle false) (stateAt 8) = some (stateAt 9) := by
  have generated : run 4 (cycle false) (stateAt 8) = some { stateAt 9 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 8 (checkpoint 8)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 8 (checkpoint 8)) =
      checkpoint 9 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 8 r member).symm
  rw [registers] at generated
  exact generated

/-- Complete generated cycle 10: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_9 : run 4 (cycle false) (stateAt 9) = some (stateAt 10) := by
  have generated : run 4 (cycle false) (stateAt 9) = some { stateAt 10 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 9 (checkpoint 9)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 9 (checkpoint 9)) =
      checkpoint 10 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 9 r member).symm
  rw [registers] at generated
  exact generated

/-- Complete generated cycle 11: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_10 : run 4 (cycle false) (stateAt 10) = some (stateAt 11) := by
  have generated : run 4 (cycle false) (stateAt 10) = some { stateAt 11 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 10 (checkpoint 10)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 10 (checkpoint 10)) =
      checkpoint 11 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 10 r member).symm
  rw [registers] at generated
  exact generated

/-- Complete generated cycle 12: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_11 : run 4 (cycle false) (stateAt 11) = some (stateAt 12) := by
  have generated : run 4 (cycle false) (stateAt 11) = some { stateAt 12 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 11 (checkpoint 11)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 11 (checkpoint 11)) =
      checkpoint 12 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 11 r member).symm
  rw [registers] at generated
  exact generated

/-- Complete generated cycle 13: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_12 : run 4 (cycle false) (stateAt 12) = some (stateAt 13) := by
  have generated : run 4 (cycle false) (stateAt 12) = some { stateAt 13 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 12 (checkpoint 12)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 12 (checkpoint 12)) =
      checkpoint 13 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 12 r member).symm
  rw [registers] at generated
  exact generated

/-- Complete generated cycle 14: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_13 : run 4 (cycle false) (stateAt 13) = some (stateAt 14) := by
  have generated : run 4 (cycle false) (stateAt 13) = some { stateAt 14 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 13 (checkpoint 13)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 13 (checkpoint 13)) =
      checkpoint 14 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 13 r member).symm
  rw [registers] at generated
  exact generated

end Xv6.Kernel.MycpuBareWitness
