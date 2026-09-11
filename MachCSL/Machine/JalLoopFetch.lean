import MachCSL.Machine.JalLoopFetchEval
import MachCSL.Machine.JalLoopBootFacts
import MachCSL.Machine.Platform

/-! Checked fetch certificate for the exact static register slice read by the
actual generated instruction fetch. All other registers remain arbitrary. -/
namespace MachCSL.Machine.JalLoop
open LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def fetchSnapshot (hart : BitVec 64) : Snapshot
  | .PC => some jalImage.vector
  | .misa => some 0x800000000014112d#64
  | .mstatus => some 0xA00000000#64
  | .cur_privilege => some .Machine
  | .pma_regions => some (bootRegisters jalImage.vector hart .pma_regions)
  | .pmpcfg_n => some (bootRegisters jalImage.vector hart .pmpcfg_n)
  | .pmpaddr_n => some (bootRegisters jalImage.vector hart .pmpaddr_n)
  | .htif_tohost_base => some (bootRegisters jalImage.vector hart .htif_tohost_base)
  | _ => none

theorem fetchSnapshot_covers (cpu : CPU) (d : Dynamic) :
    Covers (fetchSnapshot (BitVec.ofNat 64 cpu.val)) (registers cpu d) := by
  have h := boot_static (BitVec.ofNat 64 cpu.val)
  simp only [Prod.mk.injEq] at h
  intro r value hv
  cases r <;> simp only [fetchSnapshot, Option.some.injEq] at hv
  all_goals first | contradiction | subst value
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (bootRegisters_pc _ _).1
  · exact h.1
  · exact bootRegisters_misa _ _
  · exact h.2.2.2.2.2.2.2.1

/-- The checked partial evaluator rejects unlisted reads, all writes, device
reads and exclusive reads. Its success therefore certifies this actual fetch. -/
private theorem fetch_hart_0 [Platform] :
    snapshotRun (loadedRam jalImage) (fetchSnapshot 0#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_hart_1 [Platform] :
    snapshotRun (loadedRam jalImage) (fetchSnapshot 1#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_hart_2 [Platform] :
    snapshotRun (loadedRam jalImage) (fetchSnapshot 2#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_hart_3 [Platform] :
    snapshotRun (loadedRam jalImage) (fetchSnapshot 3#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_hart_4 [Platform] :
    snapshotRun (loadedRam jalImage) (fetchSnapshot 4#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_hart_5 [Platform] :
    snapshotRun (loadedRam jalImage) (fetchSnapshot 5#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_hart_6 [Platform] :
    snapshotRun (loadedRam jalImage) (fetchSnapshot 6#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem fetch_hart_7 [Platform] :
    snapshotRun (loadedRam jalImage) (fetchSnapshot 7#64) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

theorem fetch_certificate [Platform] (cpu : CPU) :
    snapshotRun (loadedRam jalImage) (fetchSnapshot (BitVec.ofNat 64 cpu.val)) 1000
      (fetch ()) = some (.F_Base 0x6f#32) := by
  obtain ⟨cpu, bound⟩ := cpu
  have cases : cpu = 0 ∨ cpu = 1 ∨ cpu = 2 ∨ cpu = 3 ∨ cpu = 4 ∨ cpu = 5 ∨ cpu = 6 ∨ cpu = 7 := by
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fetch_hart_0
  · exact fetch_hart_1
  · exact fetch_hart_2
  · exact fetch_hart_3
  · exact fetch_hart_4
  · exact fetch_hart_5
  · exact fetch_hart_6
  · exact fetch_hart_7

theorem fetch_registers [Platform] (cpu : CPU) (d : Dynamic) :
    FetchExec (loadedRam jalImage) (fetch ()) (registers cpu d)
      (.F_Base 0x6f#32) (registers cpu d) :=
  snapshotRun_exec _ _ _ (fetchSnapshot_covers cpu d) _ _ _ (fetch_certificate cpu)

end MachCSL.Machine.JalLoop
