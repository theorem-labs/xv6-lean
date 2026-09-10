import MachCSL.Machine.ColdBoot

/-! Actual generated boot-state projections. The arithmetic certificate is
separate from the generated-program projection to keep kernel checking small. -/
namespace MachCSL.Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem boot_pc (vector hart : BitVec 64) :
    (bootResult vector hart).map (fun (_, rs) => (rs .PC, rs .nextPC)) =
      some (vector, vector) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

/-- The bit updates of the generated `reset_misa`, starting at the board's MXL.
This expression is only a projection certificate; the executed program remains
`bootProgram` and is related to it below by kernel conversion. -/
private def misaResetValue : BitVec 64 :=
  let m := 0x8000000000000000#64
  let m := _root_.Sail.BitVec.updateSubrange m 0 0
    (LeanPaperStock.Functions.bool_to_bit (LeanPaperStock.Functions.hartSupports .Ext_A))
  let m := _root_.Sail.BitVec.updateSubrange m 2 2
    (LeanPaperStock.Functions.bool_to_bit (LeanPaperStock.Functions.hartSupports .Ext_C))
  let m := _root_.Sail.BitVec.updateSubrange m 1 1
    (LeanPaperStock.Functions.bool_to_bit (LeanPaperStock.Functions.hartSupports .Ext_B))
  let m := _root_.Sail.BitVec.updateSubrange m 12 12
    (LeanPaperStock.Functions.bool_to_bit (LeanPaperStock.Functions.hartSupports .Ext_M))
  let m := _root_.Sail.BitVec.updateSubrange m 20 20
    (LeanPaperStock.Functions.bool_to_bit (LeanPaperStock.Functions.hartSupports .Ext_U))
  let m := _root_.Sail.BitVec.updateSubrange m 18 18
    (LeanPaperStock.Functions.bool_to_bit (LeanPaperStock.Functions.hartSupports .Ext_S))
  let m := _root_.Sail.BitVec.updateSubrange m 21 21
    (LeanPaperStock.Functions.bool_to_bit (LeanPaperStock.Functions.hartSupports .Ext_V))
  let m := _root_.Sail.BitVec.updateSubrange m 4 4
    (LeanPaperStock.Functions.bool_to_bit LeanPaperStock.Functions.base_E_enabled)
  let m := _root_.Sail.BitVec.updateSubrange m 8 8
    (Complement.complement (LeanPaperStock.Functions._get_Misa_E m))
  let m := _root_.Sail.BitVec.updateSubrange m 5 5
    (LeanPaperStock.Functions.bool_to_bit (LeanPaperStock.Functions.hartSupports .Ext_F))
  _root_.Sail.BitVec.updateSubrange m 3 3
    (LeanPaperStock.Functions.bool_to_bit (LeanPaperStock.Functions.hartSupports .Ext_D))

private theorem boot_misa_projection (vector hart : BitVec 64) :
    (bootResult vector hart).map (fun (_, rs) => rs .misa) = some misaResetValue := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

private theorem misaResetValue_eq : misaResetValue = 0x800000000014112d#64 := by
  cbv

theorem boot_misa (vector hart : BitVec 64) :
    (bootResult vector hart).map (fun (_, rs) => rs .misa) =
      some 0x800000000014112d#64 := by
  rw [boot_misa_projection, misaResetValue_eq]

/-- The extracted successful register file contains the requested reset PC. -/
theorem bootRegisters_pc (vector hart : BitVec 64) :
    bootRegisters vector hart .PC = vector ∧
      bootRegisters vector hart .nextPC = vector := by
  have h := boot_pc vector hart
  rw [bootResult_eq] at h
  exact Prod.mk.inj (Option.some.inj h)

/-- The extracted file has the MISA computed by actual generated reset code. -/
theorem bootRegisters_misa (vector hart : BitVec 64) :
    bootRegisters vector hart .misa = 0x800000000014112d#64 := by
  have h := boot_misa vector hart
  rw [bootResult_eq] at h
  exact Option.some.inj h

end MachCSL.Machine
