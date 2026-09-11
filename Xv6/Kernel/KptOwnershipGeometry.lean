import Xv6.Kernel.KptOwnershipSpec
import Xv6.Kernel.PtTreeGeometry

namespace Xv6.Kernel.KptOwnership
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

theorem pageBase_value (b : PPN) : (pageBase b).toNat = b.toNat * 4096 := by
  change (BitVec.setWidth 64 (BitVec.append b 0#12)).toNat = _
  erw [BitVec.toNat_setWidth_of_le (by decide), @BitVec.toNat_append 44 12 b 0#12]
  simp [Nat.shiftLeft_eq]

theorem pageBase_aligned (b : PPN) : (pageBase b).toNat % pageSize = 0 := by
  rw [pageBase_value]
  simp [pageSize]

theorem valid_nodeData (b : PPN) (valid : PageValid (pageBase b)) : NodeData b := by
  rcases valid with ⟨_, lower, upper⟩
  rw [pageBase_value] at lower upper
  change (0x800235c8 : Int) ≤ (b.toNat * 4096 : Nat) at lower
  change ((b.toNat * 4096 : Nat) : Int) < (0x88000000 : Int) at upper
  unfold NodeData
  omega

theorem valid_ne_zero (p : PhysicalAddress) (valid : PageValid p) : p ≠ 0#64 := by
  intro eq
  subst p
  have lower := valid.2.1
  change (0x800235c8 : Int) ≤ 0 at lower
  omega

theorem index_lookup_nat (k : Nat) (hk : k < 512) : indices[k]? = some (BitVec.ofNat 9 k) := by
  simp [indices, hk]

theorem index_lookup (i : Index) : indices[i.toNat]? = some i := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using index_lookup_nat i.toNat i.isLt

theorem indices_nodup : indices.Nodup := by
  unfold indices
  apply FromMathlib.Nodup.map_on _ List.nodup_range
  intro x hx y hy eq
  have hx : x < 512 := List.mem_range.mp hx
  have hy : y < 512 := List.mem_range.mp hy
  have e := congrArg BitVec.toNat eq
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using e

theorem indices_length : indices.length = 512 := by simp [indices]

/-- Equal index values imply equal list positions, including the selected
position i.toNat. Used to reassemble every unmodified slot/child. -/
theorem index_lookup_position (k : Nat) (i : Index) (found : indices[k]? = some i) : k = i.toNat := by
  have hk : k < indices.length := List.getElem?_eq_some_iff.mp found |>.1
  rw [indices_length] at hk
  have equal := Option.some.inj ((index_lookup_nat k hk).symm.trans found)
  have e := congrArg BitVec.toNat equal
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] using e

theorem aligned_iff (a : PhysicalAddress) :
    is_aligned_paddr (.Physaddr a) 8 = true ↔ TsoContextWord.Aligned a := by
  change ((Int.tmod (a.toNat : Int) 8) == 0) = true ↔ a.toNat % 8 = 0
  change ((((a.toNat % 8 : Nat) : Int) == 0) = true) ↔ a.toNat % 8 = 0
  rw [beq_iff_eq]
  exact Int.ofNat_inj

theorem geometrySpec : GeometrySpec :=
  ⟨pageBase_value, pageBase_aligned, valid_nodeData, valid_ne_zero,
    index_lookup, indices_nodup, indices_length⟩

end Xv6.Kernel.KptOwnership
