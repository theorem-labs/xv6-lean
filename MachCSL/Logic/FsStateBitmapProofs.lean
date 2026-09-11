import MachCSL.Logic.FsStateBitmapDefs
import MachCSL.Logic.FsViewProofs

namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Xv6.Fs FsView
variable {GF : BundledGFunctors} (view : View GF)

instance poolElt_timeless [GTimeless view] used b : Timeless (poolElt view used b) := by
  unfold poolElt; split <;> infer_instance
instance freePool_timeless [GTimeless view] nb used : Timeless (freePool view nb used) := by
  unfold freePool; infer_instance
instance freePoolBut_timeless [GTimeless view] nb used i0 : Timeless (freePoolBut view nb used i0) := by
  unfold freePoolBut
  have (k : Nat) (b : Int) : Timeless (if k = i0 then (emp : IProp GF) else poolElt view used b) := by
    split <;> infer_instance
  infer_instance
instance freeBitmapAt_timeless [GTimeless view] bms nb used : Timeless (freeBitmapAt view bms nb used) := by
  unfold freeBitmapAt; infer_instance
instance freeBitmap_timeless [GTimeless view] sb used : Timeless (freeBitmap view sb used) := by
  unfold freeBitmap; infer_instance

theorem freeBitmap_unfold sb used : freeBitmap view sb used = freeBitmapAt view sb.bmapstart sb.size used := rfl
theorem freeBitmapAt_names (g t : GName) bms nb used :
    freeBitmapAt view bms nb used = freeBitmapAt ⟨view.phi, g, t⟩ bms nb used := rfl

theorem poolIndices_lookup (nb : Int) (i : Nat) (bound : (i : Int) < nb) :
    (poolIndices nb)[i]? = some (i : Int) := by
  have lt : i < nb.toNat := by omega
  simp [poolIndices, List.getElem?_range lt]

theorem poolIndices_mem (nb b : Int) : b ∈ poolIndices nb ↔ 0 ≤ b ∧ b < nb := by
  simp only [poolIndices, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; change 0 ≤ (i : Int) ∧ (i : Int) < nb; omega
  · intro h; exact ⟨b.toNat, by omega, Int.toNat_of_nonneg h.1⟩

theorem poolIndices_negative nb (bound : nb ≤ 0) : poolIndices nb = [] := by
  have h : nb.toNat = 0 := by omega
  simp [poolIndices, h]

theorem poolElt_used used b (found : b ∈ used) : poolElt view used b = emp := by simp [poolElt, found]
theorem poolElt_free used b (absent : b ∉ used) :
    poolElt view used b = iprop(∃ bytes, blockOwned view b bytes) := by simp [poolElt, absent]

theorem freePool_split nb used (i0 : Nat) (bound : (i0 : Int) < nb) :
    freePool view nb used ⊣⊢ poolElt view used (i0 : Int) ∗ freePoolBut view nb used i0 := by
  unfold freePool freePoolBut
  exact BigSepL.bigSepL_delete_cond (poolIndices_lookup nb i0 bound)

theorem freePool_lookup nb used b (bound : 0 ≤ b ∧ b < nb) :
    freePool view nb used ⊢ poolElt view used b := by
  unfold freePool
  have h := poolIndices_lookup nb b.toNat (by omega)
  have cast : (b.toNat : Int) = b := by omega
  rw [cast] at h
  exact BigSepL.bigSepL_lookup h

/-- A full pool block conflicts with every separately owned valid share;
the used-bit conclusion is derived from native byte exclusion. -/
theorem freePool_usedQ (exclusive : PhiExcl view) dq nb used b bytes
    (bound : 0 ≤ b ∧ b < nb) :
    iprop(⊢ freePool view nb used -∗ blockOwnedQ view dq b bytes -∗ ⌜b ∈ used⌝) := by
  by_cases found : b ∈ used
  · iintro _ _; ipureintro; exact found
  · iintro Hpool Hblock
    ihave Hpool := freePool_lookup view nb used b bound $$ Hpool
    rw [poolElt_free view used b found]
    icases Hpool with ⟨%other, Hother⟩
    ihave HotherQ := (BIBase.BiEntails.of_eq (blockOwned_one view b other)).mp $$ Hother
    ihave Hfalse := blockOwnedQ_excl view exclusive (.own 1) dq b other bytes
      (dfrac_full_invalid dq) $$ HotherQ Hblock
    icases Hfalse with ⟨⟩

end MachCSL.Logic.FsState
