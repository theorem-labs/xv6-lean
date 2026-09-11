import Xv6.Kernel.KptPublishSpec
import MachCSL.Machine.PteCanonicalProofs

namespace Xv6.Kernel.KptPublish
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

/-- Raw invalid entries and arbitrary offsets are included, exactly as source. -/
theorem slot_set_self (word : BitVec 64) (j : Nat) :
    nthByte word j ∈ PteCanonical.slotSet word j := by
  unfold PteCanonical.slotSet
  by_cases zero : j = 0
  · subst j
    simp only [↓reduceIte]
    cases hn : PteCanonical.nonleaf word with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have h := PteCanonical.adByte0_variant word
        (_get_PTE_Flags_A (PteCanonical.flags word)) (_get_PTE_Flags_D (PteCanonical.flags word))
      simpa only [PteCanonical.setAD_refl] using h
  · simp [zero]

theorem pureSpec : PureSpec := ⟨slot_set_self⟩

end Xv6.Kernel.KptPublish
