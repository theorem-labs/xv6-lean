import Xv6.Kernel.PtTreeSpec

namespace Xv6.Kernel.PtTree
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem index_injective (x y : VPN) (h2 : index 2 x = index 2 y)
    (h1 : index 1 x = index 1 y) (h0 : index 0 x = index 0 y) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases low : i < 9
  · have h := congrArg (fun v : Index => v.getLsbD i) h0
    simpa [index, BitVec.getLsbD_extractLsb, low] using h
  · by_cases mid : i < 18
    · have j : i - 9 < 9 := by omega
      have h := congrArg (fun v : Index => v.getLsbD (i - 9)) h1
      simpa [index, BitVec.getLsbD_extractLsb, j, show 9 + (i - 9) = i by omega] using h
    · have j : i - 18 < 9 := by omega
      have h := congrArg (fun v : Index => v.getLsbD (i - 18)) h2
      simpa [index, BitVec.getLsbD_extractLsb, j, show 18 + (i - 18) = i by omega] using h

/-- Append arithmetic also used by the direct-slot walker; here it is checked
for the arbitrary source-tree carrier, independently of any map ownership. -/
theorem address_value (b : PPN) (i : Index) :
    (slotAddress b i).toNat = b.toNat * 4096 + i.toNat * 8 := by
  have low : (BitVec.append i 0#3).toNat = i.toNat * 8 := by
    erw [@BitVec.toNat_append 9 3 i 0#3]
    simp [Nat.shiftLeft_eq]
  change (BitVec.setWidth 64 (BitVec.append b (BitVec.append i 0#3))).toNat = _
  erw [BitVec.toNat_setWidth_of_le (by decide), @BitVec.toNat_append 44 12 b (BitVec.append i 0#3)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.append i 0#3).isLt b.toNat, low]
  simp [Nat.shiftLeft_eq]

theorem address_aligned (b : PPN) (i : Index) :
    is_aligned_paddr (.Physaddr (slotAddress b i)) 8 = true := by
  change ((Int.tmod ((slotAddress b i).toNat : Int) 8) == 0) = true
  change ((((slotAddress b i).toNat % 8 : Nat) : Int) == 0) = true
  rw [address_value]
  simp [Nat.add_mod, Nat.mul_mod]

end Xv6.Kernel.PtTree
