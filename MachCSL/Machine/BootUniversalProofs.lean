import MachCSL.Machine.BootUniversalDefs
import MachCSL.Machine.BootUniversalRun

namespace MachCSL.Machine.BootUniversal
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def computedMisa : BitVec 64 :=
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


private def computedStatus : BitVec 64 :=
  _root_.Sail.BitVec.updateSubrange
    (_root_.Sail.BitVec.updateSubrange 0xA00000000#64 3 3 0#1) 17 17 0#1
private theorem computedMisa_eq : computedMisa = 0x800000000014112d#64 := by cbv
private theorem computedStatus_eq : computedStatus = 0xA00000000#64 := by cbv

private theorem projection_raw (before : RegisterFile) (vector hart : BitVec 64) :
    (result before vector hart).map (fun (_, rs) => staticProjection rs) =
      some (vector, vector, computedMisa, computedStatus,
        0#64, 0#64, 0#64, 0#1, 0#64, Privilege.Machine, HartState.HART_ACTIVE (), pmaBoot, none) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

theorem static_projection (before : RegisterFile) (vector hart : BitVec 64) :
    (result before vector hart).map (fun (_, rs) => staticProjection rs) =
      some (vector, vector, 0x800000000014112d#64, 0xA00000000#64,
        0#64, 0#64, 0#64, 0#1, 0#64, Privilege.Machine, HartState.HART_ACTIVE (), pmaBoot, none) := by
  simpa only [computedMisa_eq, computedStatus_eq] using projection_raw before vector hart

theorem succeeds (before : RegisterFile) (vector hart : BitVec 64) :
    (result before vector hart).isSome = true := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl


/-- Every completed source Run has the static postcondition, for any original
registers, bus, RAM and device state. -/
theorem run_static (bus : Bus Device) (before : RegisterFile) (vector hart : BitVec 64)
    (memory : Memory.ByteMap 64) (devices : Device) (after : ViewState Device)
    (run : Run bus (bootProgram vector hart pmaBoot) ⟨before, memory, devices⟩ () after) :
    StaticBoot vector after.registers := by
  cases eq : result before vector hart with
  | none =>
    have h := succeeds before vector hart
    simp only [eq, Option.isSome_none, Bool.false_eq_true] at h
  | some pair =>
    obtain ⟨u, registers⟩ := pair
    cases u
    have unique := registerRun_unique bus 10000 _ before registers () () memory devices after eq run
    have same := congrArg ViewState.registers unique.2
    rw [same]
    have projected := static_projection before vector hart
    rw [eq] at projected
    have h := Option.some.inj projected
    simp only [staticProjection, Prod.mk.injEq] at h
    obtain ⟨pc, nextPC, misa, status, mie, mideleg, menvcfg, elp, mseccfg, priv, active, pma, htif⟩ := h
    exact ⟨pc, nextPC, misa, status, mie, mideleg, menvcfg, elp, mseccfg, priv, active, pma, htif⟩

/-- Universal reset facts for the actual nondeterministic power-on predicate.
This does not replace its arbitrary preboot file with zeroRegisters. -/
theorem bootFacts_static (image : BootImage) (g : State) (facts : BootFacts image g) (cpu : CPU) :
    StaticBoot image.vector (g.registers cpu) := by
  obtain ⟨before, after, run, eq⟩ := facts.2.2.1 cpu
  rw [eq]
  exact run_static Devices.bus before image.vector (BitVec.ofNat 64 cpu.val)
    Memory.empty Devices.initial ⟨after, Memory.empty, Devices.initial⟩ run

end MachCSL.Machine.BootUniversal
