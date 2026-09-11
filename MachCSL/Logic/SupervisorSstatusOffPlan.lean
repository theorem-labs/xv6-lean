import MachCSL.Logic.SupervisorSstatusOffPure
namespace MachCSL.Logic.SupervisorSstatusOff
open Iris MachCSL.Machine LeanPaperStock.Functions
open _root_.Sail.ConcurrencyInterfaceV1.Free
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false in
/-- Every generated MISA read is retained, including eager VM tests and
invalid nominal-MPP fallback. The status arguments and all other registers
are arbitrary. -/
theorem legalize_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (dq : DFrac)
 (member : (.misa,dq) ∈ fp) (hm : rs .misa = misaValue) (old value : BitVec 64) :
 RegisterPlan.Returns fp rs (legalize_mstatus old value) (legalized old value) rs := by
 have cases : (_get_Mstatus_MPP value).toNat = 0 ∨ (_get_Mstatus_MPP value).toNat = 1 ∨
   (_get_Mstatus_MPP value).toNat = 2 ∨ (_get_Mstatus_MPP value).toNat = 3 := by
   have := (_get_Mstatus_MPP value).isLt
   omega
 rcases cases with h | h | h | h
 all_goals
   first
   | have heq : _get_Mstatus_MPP value = 0#2 := BitVec.eq_of_toNat_eq h
   | have heq : _get_Mstatus_MPP value = 1#2 := BitVec.eq_of_toNat_eq h
   | have heq : _get_Mstatus_MPP value = 2#2 := BitVec.eq_of_toNat_eq h
   | have heq : _get_Mstatus_MPP value = 3#2 := BitVec.eq_of_toNat_eq h
   simp only [legalize_mstatus, Mk_Mstatus, heq, have_nominal_privLevel,
     lowest_supported_privLevel, virtual_memory_supported, currentlyEnabled]
   repeat first
     | apply RegisterPlan.Plan.read member
       simp only [hm, misaValue, hartSupports, _get_Misa_S, _get_Misa_U,
         Sail.ArchSem.FreeM.bind, Sail.BitVec.extractLsb]
       simp only [show (0x800000000014112d#64).extractLsb 18 18 = 1#1 from rfl,
         show (0x800000000014112d#64).extractLsb 20 20 = 1#1 from rfl]
       simp only [Bool.and_self, Bool.true_and, Bool.and_true, Bool.or_true, Bool.true_or, Bool.false_or, Bool.or_false, beq_self_eq_true, ite_true, ite_false]
     | exact RegisterPlan.Plan.pure ⟨by simp [legalized, SupervisorBits.haveNominalValue, heq], rfl⟩


theorem off_plan (fp : RegisterFootprint.Footprint) (rs : RegisterFile) (dq : DFrac)
    (member : (.misa, dq) ∈ fp) (hm : rs .misa = misaValue) (ms : BitVec 64)
    (facts : SupervisorBits.MsFacts ms) (off : _get_Mstatus_SIE ms = 0#1) :
    RegisterPlan.Returns fp rs (program ms) ms rs := by
  unfold program legalize_sstatus
  have lift : lift_sstatus ms (Mk_Sstatus (zero_extend (m := 64) (writeValue ms))) = ms := by
    change lift_sstatus ms ((writeValue ms).setWidth 64) = ms
    rw [BitVec.setWidth_eq, write_value ms off, lift_lower ms facts]
  rw [lift]
  have plan := legalize_plan fp rs dq member hm ms ms
  rw [legalized_self ms facts] at plan
  exact plan

end MachCSL.Logic.SupervisorSstatusOff
