import MachCSL.Machine.JalLoopFetchEval
import MachCSL.Machine.JalLoopBootFacts

/-! Checked decode and execution of JAL x0,0, using the actual generated model. -/
namespace MachCSL.Machine.JalLoop
open LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def decodeSnapshot : Snapshot
  | .cur_privilege => some .Machine
  | .mseccfg => some 0#64
  | _ => none

theorem decode_certificate :
    snapshotRun (loadedRam jalImage) decodeSnapshot 1000 (ext_decode 0x6f#32) =
      some (.JAL (0#21, .Regidx 0#5)) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private def instructionStatic (base : RegisterFile) (r : Register) : RegisterType r :=
  match r with
  | .PC => jalImage.vector
  | .misa => 0x800000000014112d#64
  | other => base other

private theorem execute_static [Platform] (base : RegisterFile) :
    registerRun 100 (execute_JAL 0#21 (.Regidx 0#5)) (instructionStatic base) =
      some (.Retire_Success (), Sail.Registers.write (instructionStatic base) .nextPC jalImage.vector) := by
  cbv

private theorem instructionStatic_eq (base : RegisterFile)
    (pc : base .PC = jalImage.vector)
    (misa : base .misa = 0x800000000014112d#64) : instructionStatic base = base := by
  funext r
  cases r <;> simp only [instructionStatic, pc, misa]

theorem execute_JAL_exec [Platform] (rs : RegisterFile)
    (pc : rs .PC = jalImage.vector)
    (misa : rs .misa = 0x800000000014112d#64) :
    RegisterExec (execute_JAL 0#21 (.Regidx 0#5)) rs (.Retire_Success ())
      (Sail.Registers.write rs .nextPC jalImage.vector) := by
  have h := execute_static rs
  rw [instructionStatic_eq rs pc misa] at h
  exact registerRun_exec _ _ _ _ _ h

private theorem boot_instruction_projection (hart : BitVec 64) :
    (bootResult jalImage.vector hart).map (fun (_, rs) => (rs .mseccfg, rs .elp)) =
      some (0#64, 0#1) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

theorem boot_instruction_static (hart : BitVec 64) :
    bootRegisters jalImage.vector hart .mseccfg = 0#64 ∧
      bootRegisters jalImage.vector hart .elp = 0#1 := by
  have h := boot_instruction_projection hart
  rw [bootResult_eq] at h
  exact Prod.mk.inj (Option.some.inj h)

theorem decodeSnapshot_covers (cpu : CPU) (d : Dynamic) :
    Covers decodeSnapshot (registers cpu d) := by
  have h := boot_static (BitVec.ofNat 64 cpu.val)
  simp only [Prod.mk.injEq] at h
  intro r value hv
  cases r <;> simp only [decodeSnapshot, Option.some.injEq] at hv
  all_goals first | contradiction | subst value
  · exact (boot_instruction_static _).1
  · exact h.2.2.2.2.2.2.2.1

theorem decode_registers (cpu : CPU) (d : Dynamic) :
    FetchExec (loadedRam jalImage) (ext_decode 0x6f#32) (registers cpu d)
      (.JAL (0#21, .Regidx 0#5)) (registers cpu d) :=
  snapshotRun_exec _ _ _ (decodeSnapshot_covers cpu d) _ _ _ decode_certificate

end MachCSL.Machine.JalLoop
