import MachCSL.Machine.JalLoopDefs
import MachCSL.Machine.ColdBootFacts

/-! Kernel-checked static projections of the real generated boot, factored to
avoid reducing the reset program at every symbolic instruction register read. -/
namespace MachCSL.Machine.JalLoop
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def statusReset : BitVec 64 :=
  _root_.Sail.BitVec.updateSubrange
    (_root_.Sail.BitVec.updateSubrange 0xA00000000#64 3 3 0#1) 17 17 0#1

private theorem statusReset_eq : statusReset = 0xA00000000#64 := by cbv

private theorem boot_static_projection (hart : BitVec 64) :
    (bootResult jalImage.vector hart).map (fun (_, rs) =>
      (rs .mstatus, rs .mie, rs .mideleg, rs .mcountinhibit, rs .mcyclecfg,
        rs .minstretcfg, rs .menvcfg, rs .cur_privilege, rs .hart_state)) =
    some (statusReset, 0#64, 0#64, 0#32, 0#64, 0#64, 0#64,
      Privilege.Machine, HartState.HART_ACTIVE ()) := by
  run_tac Lean.Elab.Tactic.liftMetaFinishingTactic fun g =>
    Lean.Meta.withTransparency .all g.refl

theorem boot_static (hart : BitVec 64) :
    let rs := bootRegisters jalImage.vector hart
    (rs .mstatus, rs .mie, rs .mideleg, rs .mcountinhibit, rs .mcyclecfg,
      rs .minstretcfg, rs .menvcfg, rs .cur_privilege, rs .hart_state) =
    (0xA00000000#64, 0#64, 0#64, 0#32, 0#64, 0#64, 0#64,
      Privilege.Machine, HartState.HART_ACTIVE ()) := by
  have h := boot_static_projection hart
  rw [bootResult_eq, statusReset_eq] at h
  exact Option.some.inj h

end MachCSL.Machine.JalLoop
