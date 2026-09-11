import Xv6.Kernel.PtTreeWordProofs

namespace Xv6.Kernel.PtTree
open MachCSL.Machine MachCSL.Logic LeanPaperStock.Functions

theorem pointer_fields (w : Word) (valid : Valid w) (pointer : Pointer w) :
    ext_bits_of_PTE w = 0#10 ∧
    _get_PTE_Flags_V (PteCanonical.flags w) = 1#1 ∧
    _get_PTE_Flags_A (PteCanonical.flags w) = 0#1 ∧
    _get_PTE_Flags_D (PteCanonical.flags w) = 0#1 ∧
    _get_PTE_Flags_U (PteCanonical.flags w) = 0#1 := by
  let rs : RegisterFile := fun r => by cases r <;> exact default
  have good := outcome_value w false valid rs
  change pte_is_non_leaf (PteCanonical.flags w) = true at pointer
  have reserved : pte_reserved_bits_must_be_zero = true := rfl
  simp only [invalidValue, pointer, reserved,
    Bool.true_and, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    beq_eq_false_iff_ne, bne_eq_false_iff_eq] at good
  rcases good with ⟨v, _, _, _, ⟨a, d, u, ext⟩, _⟩
  refine ⟨ext, ?_, ?_, ?_, ?_⟩
  · rcases PteCanonical.bit1_cases (_get_PTE_Flags_V (PteCanonical.flags w)) with h | h
    · exact False.elim (v h)
    · exact h
  · rcases PteCanonical.bit1_cases (_get_PTE_Flags_A (PteCanonical.flags w)) with h | h
    · exact h
    · exact False.elim (a h)
  · rcases PteCanonical.bit1_cases (_get_PTE_Flags_D (PteCanonical.flags w)) with h | h
    · exact h
    · exact False.elim (d h)
  · rcases PteCanonical.bit1_cases (_get_PTE_Flags_U (PteCanonical.flags w)) with h | h
    · exact h
    · exact False.elim (u h)

theorem pointer_ext_zero (w : Word) (valid : Valid w) (pointer : Pointer w) :
    ext_bits_of_PTE w = 0#10 := (pointer_fields w valid pointer).1

theorem pointer_flags (w : Word) (valid : Valid w) (pointer : Pointer w) :
    _get_PTE_Flags_V (PteCanonical.flags w) = 1#1 ∧
    _get_PTE_Flags_A (PteCanonical.flags w) = 0#1 ∧
    _get_PTE_Flags_D (PteCanonical.flags w) = 0#1 ∧
    _get_PTE_Flags_U (PteCanonical.flags w) = 0#1 := (pointer_fields w valid pointer).2

theorem pointer_rwx (w : Word) (pointer : Pointer w) :
    _get_PTE_Flags_R (PteCanonical.flags w) = 0#1 ∧
    _get_PTE_Flags_W (PteCanonical.flags w) = 0#1 ∧
    _get_PTE_Flags_X (PteCanonical.flags w) = 0#1 := by
  have h : _get_PTE_Flags_X (PteCanonical.flags w) = 0#1 ∧
      _get_PTE_Flags_W (PteCanonical.flags w) = 0#1 ∧
      _get_PTE_Flags_R (PteCanonical.flags w) = 0#1 := by
    simpa [Pointer, PteCanonical.nonleaf, pte_is_non_leaf] using pointer
  exact ⟨h.2.2, h.2.1, h.1⟩

theorem pointer_validation_plan (w : Word) (valid : Valid w) (pointer : Pointer w)
    (rs : RegisterFile) : RegisterPlan.Returns [] rs (validation w) false rs := by
  obtain ⟨ext, v, a, d, u⟩ := pointer_fields w valid pointer
  obtain ⟨r, ww, x⟩ := pointer_rwx w pointer
  rw [validation_eq]
  apply RegisterPlan.Plan.readAny
  intro environment1
  apply RegisterPlan.Plan.readAny
  intro isa1
  apply RegisterPlan.Plan.readAny
  intro isa2
  apply RegisterPlan.Plan.readAny
  intro environment2
  apply RegisterPlan.Plan.readAny
  intro isa3
  apply RegisterPlan.Plan.pure
  refine ⟨?_, rfl⟩
  simp [invalidValue, ext, v, a, d, u, r, ww, x, zeros,
    _get_PTE_Ext_PBMT, _get_PTE_Ext_N, _get_PTE_Ext_RSW_60t59b, _get_PTE_Ext_reserved,
    page_based_mem_type_forwards_matches, _root_.Sail.BitVec.extractLsb]

end Xv6.Kernel.PtTree
