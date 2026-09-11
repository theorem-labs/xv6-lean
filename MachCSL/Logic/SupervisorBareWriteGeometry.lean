import MachCSL.Machine.SupervisorPhysicalDefs
namespace MachCSL.Logic.SupervisorBareWrite
open MachCSL.Machine LeanPaperStock.Functions
theorem pageMask (a : BitVec 64) :
    a &&& ~~~ ((BitVec.allOnes 12).setWidth 64) = (a >>> 12) <<< 12 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases h : i < 12
  · simp [h]
  · simp [h, show 12 ≤ i by omega, Bool.and_comm]

theorem plus_seven_page (a : BitVec 64) (aligned : a.toNat % 8 = 0) :
    a &&& ~~~ ((BitVec.allOnes 12).setWidth 64) =
      (a + 7#64) &&& ~~~ ((BitVec.allOnes 12).setWidth 64) := by
  rw [pageMask, pageMask]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have bound := a.isLt
  have hmod : a.toNat % 4096 % 8 = 0 := by omega
  omega

theorem split_page_eight (a : BitVec 64) (aligned : a.toNat % 8 = 0) :
    split_on_page_boundary a 8 = (pure (8, 0) : SailM (Int × Int)) := by
  have mask := plus_seven_page a aligned
  unfold split_on_page_boundary
  dsimp only
  split
  · rfl
  · rename_i failed
    exfalso
    apply failed
    apply beq_iff_eq.mpr
    conv => lhs; arg 2; cbv
    conv => rhs; arg 2; cbv
    change a &&& (0xfffffffffffff000#64) =
      (_root_.Sail.BitVec.subInt (_root_.Sail.BitVec.addInt a 8) 1) &&& (0xfffffffffffff000#64)
    have shift : _root_.Sail.BitVec.subInt (_root_.Sail.BitVec.addInt a 8) 1 = a + 7#64 := by
      simp [_root_.Sail.BitVec.subInt, _root_.Sail.BitVec.addInt, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [shift]
    exact mask

end MachCSL.Logic.SupervisorBareWrite
