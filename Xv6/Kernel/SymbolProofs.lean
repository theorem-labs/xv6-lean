import Xv6.Kernel.SymbolDefs

namespace Xv6.Kernel.Symbols

theorem check_iff (f : Image.Packed) (table row : Nat) (expected : Kernel.Symbol) :
    check f table row expected = true ↔ ∃ actual,
      Elf.symbolAt f table row = some actual ∧
      actual.name = expected.elfName.toUTF8.data.toList ∧
      actual.entry.value = expected.address ∧ actual.entry.sectionIndex ≠ 0 := by
  simp only [check, Option.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
  constructor
  · rintro ⟨actual, parsed, ⟨name, value⟩, defined⟩
    exact ⟨actual, parsed, name, value, defined⟩
  · rintro ⟨actual, parsed, name, value, defined⟩
    exact ⟨actual, parsed, ⟨name, value⟩, defined⟩

end Xv6.Kernel.Symbols
