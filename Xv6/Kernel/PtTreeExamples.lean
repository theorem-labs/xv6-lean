import Xv6.Kernel.PtTreeLink

namespace Xv6.Kernel.PtTree

/-- Non-vacuity with G and both low RSW bits set. Validity has no hidden
G/RSW-zero premise, even though the direct-slot walk uses flag-one pointers. -/
theorem raw_pointer_example : Valid 0x321#64 ∧ Pointer 0x321#64 ∧
    globalBit 0x321#64 = true ∧ (0x321#64).extractLsb 9 8 = 3#2 := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro rs
  refine ⟨6, ?_⟩
  rw [validation_run]
  rfl

/-- The semantic leaf predicate admits both unset and set A/D bits. -/
theorem leaf_ad_examples : Valid 7#64 ∧ Valid 0xc7#64 ∧
    Leaf 7#64 ∧ Leaf 0xc7#64 ∧
    MachCSL.Machine.PteCanonical.canon 7#64 = MachCSL.Machine.PteCanonical.canon 0xc7#64 := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  all_goals
    intro rs
    refine ⟨6, ?_⟩
    rw [validation_run]
    rfl

/-- Zero is invalid under every register file, so absent-slot blocking is
also inhabited under the actual validator. -/
theorem zero_invalid : Invalid 0#64 := by
  intro rs
  refine ⟨6, ?_⟩
  rw [validation_run]
  rfl

end Xv6.Kernel.PtTree
