import MachCSL.Logic.SupervisorSstatusOffDefs

namespace MachCSL.Logic.SupervisorSstatusOff
open Iris MachCSL.Machine LeanPaperStock.Functions

/-- Pure normalization and finite plans for the actual legalizer. The
surrounding CSR read/write and destination register update are separate. -/
structure Spec : Prop where
  supports_landing_pad : hartSupports .Ext_Zicfilp = true
  lower_sie : ∀ ms, _get_Sstatus_SIE (lower_mstatus ms) = _get_Mstatus_SIE ms
  write_value : ∀ ms, _get_Mstatus_SIE ms = 0#1 → writeValue ms = lower_mstatus ms
  lift_lower : ∀ ms, SupervisorBits.MsFacts ms → lift_sstatus ms (lower_mstatus ms) = ms
  legalized_self : ∀ ms, SupervisorBits.MsFacts ms → legalized ms ms = ms
  result_self : ∀ ms, SupervisorBits.MsFacts ms → _get_Mstatus_SIE ms = 0#1 → result ms = ms
  result_facts : ∀ ms, SupervisorBits.MsFacts ms → _get_Mstatus_SIE ms = 0#1 →
    SupervisorBits.MsFacts (result ms)
  result_bits : ∀ ms, SupervisorBits.MsFacts ms → _get_Mstatus_SIE ms = 0#1 →
    _get_Mstatus_SIE (result ms) = 0#1 ∧
    _get_Mstatus_SPP (result ms) = _get_Mstatus_SPP ms ∧
    _get_Mstatus_SPIE (result ms) = _get_Mstatus_SPIE ms ∧
    _get_Mstatus_SPELP (result ms) = _get_Mstatus_SPELP ms ∧
    _get_Mstatus_MPELP (result ms) = _get_Mstatus_MPELP ms
  lower_sie_zero : ∀ ms, _get_Mstatus_SIE ms = 0#1 →
    _get_Sstatus_SIE (lower_mstatus ms) = 0#1
  legalize_plan : ∀ fp rs dq, (.misa, dq) ∈ fp → rs .misa = misaValue → ∀ old value,
    RegisterPlan.Returns fp rs (legalize_mstatus old value) (legalized old value) rs
  off_plan : ∀ fp rs dq, (.misa, dq) ∈ fp → rs .misa = misaValue → ∀ ms,
    SupervisorBits.MsFacts ms → _get_Mstatus_SIE ms = 0#1 →
    RegisterPlan.Returns fp rs (program ms) ms rs

end MachCSL.Logic.SupervisorSstatusOff
