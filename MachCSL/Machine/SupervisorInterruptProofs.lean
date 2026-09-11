import MachCSL.Machine.SupervisorInterruptDefs

namespace MachCSL.Machine.SupervisorInterrupt
open LeanPaperStock.Functions

theorem machine_pending_zero (rs : RegisterFile) (disabled : Disabled rs)
    (pending : BitVec 64) :
    pending &&& (rs .mie &&& ~~~(rs .mideleg)) = 0#64 := by
  rw [disabled.delegated, BitVec.and_zero]

/-- The SIE condition is precisely a disabled one-bit field, without fixing status. -/
theorem sie_zero (rs : RegisterFile) :
    (_get_Mstatus_SIE (rs .mstatus) == 1#1) = false ↔
      _get_Mstatus_SIE (rs .mstatus) = 0#1 := by
  simp only [beq_eq_false_iff_ne]
  have bound := (_get_Mstatus_SIE (rs .mstatus)).isLt
  constructor
  · intro different
    apply BitVec.eq_of_toNat_eq
    have notOne : (_get_Mstatus_SIE (rs .mstatus)).toNat ≠ 1 := by
      intro equal
      apply different
      exact BitVec.eq_of_toNat_eq equal
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  · intro zero
    rw [zero]
    decide

end MachCSL.Machine.SupervisorInterrupt
