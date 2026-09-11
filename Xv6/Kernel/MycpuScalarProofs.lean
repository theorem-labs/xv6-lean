import Xv6.Kernel.MycpuScalarDefs
import MachCSL.Logic.RegisterPlanProofs

namespace Xv6.Kernel.MycpuScalar
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem footprint_unique (pcShare tpShare : Iris.DFrac) :
    RegisterFootprint.Unique (footprint pcShare tpShare) := by
  simp [RegisterFootprint.Unique, footprint]

theorem execute_eq [Platform] (i : Fin 9) :
    execute (MycpuDecode.normalized (index i)) = program i := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g => do
      let some (_, _, rhs) := (← Lean.Meta.whnf (← g.getType)).eq? | throwError "expected equality"
      g.assign (← Lean.Meta.mkEqRefl rhs)

/-- Exact generated arithmetic execution with arbitrary unrelated register values. -/
theorem normalized_plan [Platform] (pcShare tpShare : Iris.DFrac)
    (i : Fin 9) (rs : RegisterFile) :
    RegisterPlan.Returns (footprint pcShare tpShare) rs
      (execute (MycpuDecode.normalized (index i))) (.Retire_Success ()) (after i rs) := by
  rw [execute_eq]
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .read (dq := .own 1) (by simp [footprint])
      (.write (by simp [footprint]) (.pure ⟨rfl, rfl⟩))
  · exact .read (dq := .own 1) (by simp [footprint])
      (.write (by simp [footprint]) (.pure ⟨rfl, rfl⟩))
  · exact .read (dq := tpShare) (by simp [footprint])
      (.write (by simp [footprint]) (.pure ⟨rfl, rfl⟩))
  · exact .read (dq := .own 1) (by simp [footprint])
      (.write (by simp [footprint]) (.pure ⟨rfl, rfl⟩))
  · exact .read (dq := .own 1) (by simp [footprint])
      (.write (by simp [footprint]) (.pure ⟨rfl, rfl⟩))
  · exact .read (dq := pcShare) (by simp [footprint])
      (.write (by simp [footprint]) (.pure ⟨rfl, rfl⟩))
  · exact .read (dq := .own 1) (by simp [footprint])
      (.write (by simp [footprint]) (.pure ⟨rfl, rfl⟩))
  · exact .read (dq := .own 1) (by simp [footprint])
      (.read (dq := .own 1) (by simp [footprint])
        (.write (by simp [footprint]) (.pure ⟨rfl, rfl⟩)))
  · exact .read (dq := .own 1) (by simp [footprint])
      (.write (by simp [footprint]) (.pure ⟨rfl, rfl⟩))

theorem body_eq [Platform] (i : Fin 9) :
    body i = execute (MycpuDecode.normalized (index i)) := by
  obtain ⟨i, bound⟩ := i
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem body_plan [Platform] (pcShare tpShare : Iris.DFrac)
    (i : Fin 9) (rs : RegisterFile) :
    RegisterPlan.Returns (footprint pcShare tpShare) rs (body i)
      (.Retire_Success ()) (after i rs) := by
  rw [body_eq]
  exact normalized_plan pcShare tpShare i rs

end Xv6.Kernel.MycpuScalar
