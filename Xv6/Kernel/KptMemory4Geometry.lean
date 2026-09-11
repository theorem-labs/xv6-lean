import Xv6.Kernel.KptMemory4Pure
import MachCSL.Logic.SupervisorBareWriteGeometry
namespace Xv6.Kernel.KptMemory4
open Iris MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

theorem alignment (address : BitVec 64) (aligned : KernelDatumWord4.Aligned address) :
    is_aligned_paddr (.Physaddr address) 4 = true := by
  unfold is_aligned_paddr _root_.Sail.BitVec.toNatInt
  change ((Int.tmod (address.toNat : Int) 4) == 0) = true
  have same : Int.tmod (address.toNat : Int) 4 = ((address.toNat % 4 : Nat) : Int) := rfl
  rw [same, aligned]; rfl

theorem data_range pa (aligned : KernelDatumWord4.Aligned pa) (ram : KernelDatum.Ram pa) :
    SupervisorPhysical.RamRange pa 4 := by
  unfold KernelDatumWord4.Aligned at aligned
  unfold KernelDatum.Ram at ram
  unfold SupervisorPhysical.RamRange ramLow ramHigh
  simp only [ramLow,ramHigh] at ram
  omega

theorem plus_three_page (a : BitVec 64) (aligned : a.toNat % 4 = 0) :
    a &&& ~~~ ((BitVec.allOnes 12).setWidth 64) =
      (a + 3#64) &&& ~~~ ((BitVec.allOnes 12).setWidth 64) := by
  rw [SupervisorBareWrite.pageMask, SupervisorBareWrite.pageMask]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have bound := a.isLt
  have hmod : a.toNat % 4096 % 4 = 0 := by omega
  omega

theorem split_page_four (a : BitVec 64) (aligned : a.toNat % 4 = 0) :
    split_on_page_boundary a 4 = (pure (4, 0) : SailM (Int × Int)) := by
  have mask := plus_three_page a aligned
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
      (_root_.Sail.BitVec.subInt (_root_.Sail.BitVec.addInt a 4) 1) &&& (0xfffffffffffff000#64)
    have shift : _root_.Sail.BitVec.subInt (_root_.Sail.BitVec.addInt a 4) 1 = a + 3#64 := by
      simp [_root_.Sail.BitVec.subInt, _root_.Sail.BitVec.addInt, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [shift]
    exact mask

end Xv6.Kernel.KptMemory4
