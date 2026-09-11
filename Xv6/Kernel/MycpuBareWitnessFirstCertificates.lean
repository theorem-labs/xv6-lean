import Xv6.Kernel.MycpuBareWitnessOrderProofs

namespace Xv6.Kernel.MycpuBareWitness
open MachCSL MachCSL.Machine MachCSL.Logic
attribute [local instance] platform
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- Complete generated cycle 1: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_0 : run 4 (cycle false) (stateAt 0) = some (stateAt 1) := by
  have generated : run 4 (cycle false) (stateAt 0) = some { stateAt 1 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 0 (checkpoint 0)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 0 (checkpoint 0)) =
      checkpoint 1 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 0 r member).symm
  rw [registers] at generated
  exact generated

/-- Complete generated cycle 2: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_1 : run 4 (cycle false) (stateAt 1) = some (stateAt 2) := by
  have generated : run 4 (cycle false) (stateAt 1) = some { stateAt 2 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 1 (checkpoint 1)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 1 (checkpoint 1)) =
      checkpoint 2 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 1 r member).symm
  rw [registers] at generated
  exact generated

/-- Complete generated cycle 3: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_2 : run 4 (cycle false) (stateAt 2) = some (stateAt 3) := by
  have generated : run 4 (cycle false) (stateAt 2) = some { stateAt 3 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 2 (checkpoint 2)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 2 (checkpoint 2)) =
      checkpoint 3 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 2 r member).symm
  rw [registers] at generated
  exact generated

/-- Complete generated cycle 4: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_3 : run 4 (cycle false) (stateAt 3) = some (stateAt 4) := by
  have generated : run 4 (cycle false) (stateAt 3) = some { stateAt 4 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 3 (checkpoint 3)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 3 (checkpoint 3)) =
      checkpoint 4 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 3 r member).symm
  rw [registers] at generated
  exact generated

/-- Complete generated cycle 5: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_4 : run 4 (cycle false) (stateAt 4) = some (stateAt 5) := by
  have generated : run 4 (cycle false) (stateAt 4) = some { stateAt 5 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 4 (checkpoint 4)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 4 (checkpoint 4)) =
      checkpoint 5 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 4 r member).symm
  rw [registers] at generated
  exact generated

/-- Complete generated cycle 6: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_5 : run 4 (cycle false) (stateAt 5) = some (stateAt 6) := by
  have generated : run 4 (cycle false) (stateAt 5) = some { stateAt 6 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 5 (checkpoint 5)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 5 (checkpoint 5)) =
      checkpoint 6 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 5 r member).symm
  rw [registers] at generated
  exact generated

/-- Complete generated cycle 7: the source-ordered state equation is
checked once, followed by a pure equality covering the entire register file. -/
theorem cycle_6 : run 4 (cycle false) (stateAt 6) = some (stateAt 7) := by
  have generated : run 4 (cycle false) (stateAt 6) = some { stateAt 7 with
      registers := SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 6 (checkpoint 6)) } := by
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => Lean.Meta.withTransparency .all g.refl
  have registers : SupervisorRetirement.completeAfter (MycpuBare.bodyFile entry 6 (checkpoint 6)) =
      checkpoint 7 := by
    funext r
    by_cases member : r ∈ MycpuBare.ignored
    · simp only [MycpuBare.ignored, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
        Lean.Meta.withTransparency .all g.refl
    · exact (ordered_core 6 r member).symm
  rw [registers] at generated
  exact generated

end Xv6.Kernel.MycpuBareWitness
