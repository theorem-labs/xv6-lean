import Xv6.Kernel.MycpuKptSpec
import Xv6.Kernel.MycpuKptCycleLink
import Xv6.Kernel.MycpuBareReference

namespace Xv6.Kernel.MycpuKpt
open Iris MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 10000
set_option maxHeartbeats 500000

theorem started_entry control cpu values :
    MycpuKptCycle.started (entry control cpu values) = entry (MycpuKptCycle.started control) cpu values := by
  funext r; cases r <;> rfl

theorem complete_entry control cpu values :
    SupervisorRetirement.completeAfter (entry control cpu values) =
      entry (SupervisorRetirement.completeAfter control) cpu values := by
  unfold SupervisorRetirement.completeAfter
  have flag : entry control cpu values .minstret_increment = control .minstret_increment := rfl
  rw [flag]
  split <;> funext r <;> cases r <;> rfl

theorem completed_entry before after cpu values (done : MycpuRegimeShell.Completed before after) :
    MycpuRegimeShell.Completed (entry before cpu values) (entry after cpu values) := by
  unfold MycpuRegimeShell.Completed MycpuCycleShell.completed
  rw [complete_entry]
  intro r outside
  cases r <;> first | rfl | exact done _ outside

theorem phase_bound {initial original old cpu k control values words}
    (phase : Phase initial original old cpu k control values words) : k ≤ 14 := by
  cases phase with
  | zero => omega
  | next bound _ _ => omega

theorem scalar_entry i control cpu values :
    entry (MycpuKptRegister.afterControl (.scalar i) control cpu values) cpu
      (MycpuKptRegister.afterValues (.scalar i) control cpu values) =
    MycpuScalar.after i (entry control cpu values) :=
  MycpuKptRegister.scalar_entry i control cpu values

theorem return_entry control cpu values :
    entry (MycpuKptRegister.afterControl .returns control cpu values) cpu
      (MycpuKptRegister.afterValues .returns control cpu values) =
    MycpuReturn.after (entry control cpu values) :=
  MycpuKptRegister.return_entry control cpu values

theorem load_entry control cpu values slot word :
    entry control cpu (MycpuKptMemory.afterMap .load slot values word) =
      MycpuMemory.after slot (entry control cpu values) word :=
  MycpuKptMemory.entry_load control cpu values slot word

theorem prepared_entry i control cpu values :
    MycpuKptCycle.Prepared i (entry control cpu values) = entry (MycpuKptCycle.Prepared i control) cpu values :=
  MycpuKptCycle.prepared_entry i control cpu values

theorem body_entry (initial control : RegisterFile) (original : HartTp.GprFile) (old : Words)
    (cpu : CPU) (i : Fin 14) (values : HartTp.GprFile) :
    entry (MycpuKptCycle.bodyControl i (MycpuKptCycle.started control) cpu values) cpu
      (MycpuKptCycle.bodyValues i (MycpuKptCycle.started control) cpu values (wordsAt cpu original old i.val)) =
    MycpuBare.bodyFile (entry initial cpu original) i.val (entry control cpu values) := by
  obtain ⟨i,bound⟩ := i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [MycpuKptCycle.bodyControl, MycpuKptCycle.bodyValues, MycpuKptBody.route,
    MycpuKptBody.afterControl, MycpuKptBody.afterValues]
  · rw [scalar_entry ⟨0, by decide⟩ (MycpuKptCycle.Prepared ⟨0,bound⟩ (MycpuKptCycle.started control)) cpu values]
    rw [← prepared_entry ⟨0,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · simp only [MycpuKptMemory.afterMap]
    rw [← prepared_entry ⟨1,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · simp only [MycpuKptMemory.afterMap]
    rw [← prepared_entry ⟨2,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · rw [scalar_entry ⟨1, by decide⟩ (MycpuKptCycle.Prepared ⟨3,bound⟩ (MycpuKptCycle.started control)) cpu values]
    rw [← prepared_entry ⟨3,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · rw [scalar_entry ⟨2, by decide⟩ (MycpuKptCycle.Prepared ⟨4,bound⟩ (MycpuKptCycle.started control)) cpu values]
    rw [← prepared_entry ⟨4,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · rw [scalar_entry ⟨3, by decide⟩ (MycpuKptCycle.Prepared ⟨5,bound⟩ (MycpuKptCycle.started control)) cpu values]
    rw [← prepared_entry ⟨5,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · rw [scalar_entry ⟨4, by decide⟩ (MycpuKptCycle.Prepared ⟨6,bound⟩ (MycpuKptCycle.started control)) cpu values]
    rw [← prepared_entry ⟨6,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · rw [scalar_entry ⟨5, by decide⟩ (MycpuKptCycle.Prepared ⟨7,bound⟩ (MycpuKptCycle.started control)) cpu values]
    rw [← prepared_entry ⟨7,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · rw [scalar_entry ⟨6, by decide⟩ (MycpuKptCycle.Prepared ⟨8,bound⟩ (MycpuKptCycle.started control)) cpu values]
    rw [← prepared_entry ⟨8,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · rw [scalar_entry ⟨7, by decide⟩ (MycpuKptCycle.Prepared ⟨9,bound⟩ (MycpuKptCycle.started control)) cpu values]
    rw [← prepared_entry ⟨9,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · rw [load_entry (MycpuKptCycle.Prepared ⟨10,bound⟩ (MycpuKptCycle.started control)) cpu values .ra (wordsAt cpu original old 10 .ra)]
    rw [← prepared_entry ⟨10,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · rw [load_entry (MycpuKptCycle.Prepared ⟨11,bound⟩ (MycpuKptCycle.started control)) cpu values .s0 (wordsAt cpu original old 11 .s0)]
    rw [← prepared_entry ⟨11,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · rw [scalar_entry ⟨8, by decide⟩ (MycpuKptCycle.Prepared ⟨12,bound⟩ (MycpuKptCycle.started control)) cpu values]
    rw [← prepared_entry ⟨12,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl
  · rw [return_entry (MycpuKptCycle.Prepared ⟨13,bound⟩ (MycpuKptCycle.started control)) cpu values]
    rw [← prepared_entry ⟨13,bound⟩ (MycpuKptCycle.started control) cpu values, ← started_entry control cpu values]
    rfl

theorem words_step initial control original old cpu (i : Fin 14) values
    (phase : MycpuBare.Phase (entry initial cpu original) i.val (entry control cpu values)) :
    MycpuKptCycle.bodyWords i cpu values (wordsAt cpu original old i.val) =
      wordsAt cpu original old (i.val+1) := by
  obtain ⟨i,bound⟩ := i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals funext slot; cases slot <;> try rfl
  · exact MycpuBare.phase_store_ra phase
  · exact MycpuBare.phase_store_s0 phase

theorem phase_reference {initial original old cpu k control values words}
    (phase : Phase initial original old cpu k control values words) :
    MycpuBare.Phase (entry initial cpu original) k (entry control cpu values) ∧
      words = wordsAt cpu original old k := by
  induction phase with
  | zero => exact ⟨MycpuBare.phase_zero _, by funext slot; cases slot <;> rfl⟩
  | @next k before values words after bound phase done ih =>
    rcases ih with ⟨reference, rfl⟩
    have full := completed_entry _ _ cpu
      (MycpuKptCycle.bodyValues ⟨k,bound⟩ (MycpuKptCycle.started before) cpu values (wordsAt cpu original old k)) done
    rw [body_entry initial before original old cpu ⟨k,bound⟩ values] at full
    exact ⟨MycpuBare.phase_next _ k _ _ reference full,
      words_step initial before original old cpu ⟨k,bound⟩ values reference⟩

end Xv6.Kernel.MycpuKpt
