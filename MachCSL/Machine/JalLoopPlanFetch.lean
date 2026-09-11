import MachCSL.Machine.JalLoopPlanEval
import MachCSL.Machine.JalLoopFetch

/-! A four-byte oracle for the actual fetched JAL. The oracle is deliberately
partial; its certificate establishes the complete set of RAM requests to justify. -/
namespace MachCSL.Machine.JalLoopPlan
open MachCSL.Logic.EventWP LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def CodeRead (n : Nat) (req : Logic.MemoryReadWP.ReadRequest n) (word : BitVec (8 * n)) : Prop :=
  n = 4 ∧ req.pa = jalImage.vector ∧ word = BitVec.ofNat (8 * n) 0x6f

def codeOracle : ReadOracle := fun n req =>
  if n == 4 && req.pa.toNat == jalImage.vector.toNat then some (BitVec.ofNat (8 * n) 0x6f) else none

theorem codeOracle_allowed (n : Nat) (req : Logic.MemoryReadWP.ReadRequest n)
    (word : BitVec (8 * n)) (found : codeOracle n req = some word) : CodeRead n req word := by
  unfold codeOracle at found
  split at found
  · rename_i h
    have gateNat : n = 4 ∧ req.pa.toNat = jalImage.vector.toNat := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using h
    have gate : n = 4 ∧ req.pa = jalImage.vector :=
      ⟨gateNat.1, BitVec.eq_of_toNat_eq gateNat.2⟩
    exact ⟨gate.1, gate.2, (Option.some.inj found).symm⟩
  · contradiction

private theorem fetch_checked_0 [Platform] :
    snapshotPlanRun codeOracle (JalLoop.fetchSnapshot 0#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_checked_1 [Platform] :
    snapshotPlanRun codeOracle (JalLoop.fetchSnapshot 1#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_checked_2 [Platform] :
    snapshotPlanRun codeOracle (JalLoop.fetchSnapshot 2#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_checked_3 [Platform] :
    snapshotPlanRun codeOracle (JalLoop.fetchSnapshot 3#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_checked_4 [Platform] :
    snapshotPlanRun codeOracle (JalLoop.fetchSnapshot 4#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_checked_5 [Platform] :
    snapshotPlanRun codeOracle (JalLoop.fetchSnapshot 5#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_checked_6 [Platform] :
    snapshotPlanRun codeOracle (JalLoop.fetchSnapshot 6#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_checked_7 [Platform] :
    snapshotPlanRun codeOracle (JalLoop.fetchSnapshot 7#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

/-- This initial certificate still uses each hart's concrete boot PMP slice.
The arbitrary-preboot PMP generalization is a separate obligation. -/
theorem fetch_checked [Platform] (cpu : CPU) :
    snapshotPlanRun codeOracle (JalLoop.fetchSnapshot (BitVec.ofNat 64 cpu.val)) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  obtain ⟨cpu, bound⟩ := cpu
  have cases : cpu = 0 ∨ cpu = 1 ∨ cpu = 2 ∨ cpu = 3 ∨ cpu = 4 ∨ cpu = 5 ∨ cpu = 6 ∨ cpu = 7 := by
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fetch_checked_0
  · exact fetch_checked_1
  · exact fetch_checked_2
  · exact fetch_checked_3
  · exact fetch_checked_4
  · exact fetch_checked_5
  · exact fetch_checked_6
  · exact fetch_checked_7

theorem fetch_plan [Platform] (cpu : CPU) (rs : RegisterFile)
    (covered : JalLoop.Covers (JalLoop.fetchSnapshot (BitVec.ofNat 64 cpu.val)) rs) :
    Returns CodeRead rs (fetch ()) (.F_Base 0x6f#32) rs :=
  snapshotPlanRun_plan CodeRead codeOracle codeOracle_allowed _ rs covered _ _ _ (fetch_checked cpu)

end MachCSL.Machine.JalLoopPlan
