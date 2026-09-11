import Xv6.Kernel.KernelDatumWordSpec

namespace Xv6.Kernel.KernelDatumWord
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic KernelDatum

theorem page_window va (aligned : TsoContextWord.Aligned va) : va.toNat % 4096 + 8 ≤ 4096 := by
  unfold TsoContextWord.Aligned at aligned
  omega

private theorem address_add va j (aligned : TsoContextWord.Aligned va) (bound : j < 8) :
    (addressAdd va j).toNat = va.toNat + j := by
  have size := va.isLt
  unfold TsoContextWord.Aligned at aligned
  simp only [addressAdd, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem vpn_offset va j (aligned : TsoContextWord.Aligned va) (bound : j < 8) :
    vpn (addressAdd va j) = vpn va := by
  apply BitVec.eq_of_toNat_eq
  simp only [vpn, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [address_add va j aligned bound]
  have window := page_window va aligned
  omega

private theorem physical_nat va ppn :
    (physical ppn va).toNat = ppn.toNat * 4096 + va.toNat % 4096 := by
  have size := ppn.isLt
  change ((ppn ++ va.extractLsb' 0 12).setWidth 64).toNat = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt (va.extractLsb' 0 12).isLt]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.shiftLeft_eq]
  omega

theorem physical_offset va ppn j (aligned : TsoContextWord.Aligned va) (bound : j < 8) :
    physical ppn (addressAdd va j) = addressAdd (physical ppn va) j := by
  apply BitVec.eq_of_toNat_eq
  rw [physical_nat, address_add va j aligned bound]
  simp only [addressAdd, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [physical_nat]
  have size := ppn.isLt
  have window := page_window va aligned
  omega

theorem physical_aligned va ppn (aligned : TsoContextWord.Aligned va) :
    TsoContextWord.Aligned (physical ppn va) := by
  unfold TsoContextWord.Aligned at *
  rw [physical_nat]
  omega

end Xv6.Kernel.KernelDatumWord
