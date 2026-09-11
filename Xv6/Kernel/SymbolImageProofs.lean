import Xv6.Generated.KernelSymbolCertificates
import Xv6.Kernel.MycpuDecodeDefs

namespace Xv6.Kernel.Symbols
open Xv6.Generated.KernelSymbolCertificates
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Every imported symbol's original ELF name and value occur in the actual
linked symbol/string tables. No completeness or nm-order assertion is made. -/
theorem all_imported (expected : Kernel.Symbol) (member : expected ∈ Kernel.symbols) :
    ∃ row actual, Elf.symbolAt Images.kernel tableIndex row = some actual ∧
      actual.name = expected.elfName.toUTF8.data.toList ∧
      actual.entry.value = expected.address ∧ actual.entry.sectionIndex ≠ 0 := by
  obtain ⟨i, bound, same⟩ := List.getElem_of_mem member
  have count : Kernel.symbols.length = 222 := by decide
  have checked := all_rows ⟨i, by omega⟩
  have lookup : Kernel.symbols[i]? = some expected := by
    rw [List.getElem?_eq_getElem bound, same]
  cases rowEq : rows[i]? with
  | none => simp [checkRow, lookup, rowEq] at checked
  | some row =>
    have good : check Images.kernel tableIndex row expected = true := by
      simpa [checkRow, lookup, rowEq] using checked
    obtain ⟨actual, parsed, name, value, defined⟩ := (check_iff _ _ _ _).mp good
    exact ⟨row, actual, parsed, name, value, defined⟩

theorem mycpu_symbol : Elf.symbolAt Images.kernel 18 141 =
    some ⟨"mycpu".toUTF8.data.toList, ⟨863, 18, 0, 1, MycpuDecode.base, 32⟩⟩ := by decide

theorem cpus_symbol : Elf.symbolAt Images.kernel 18 219 =
    some ⟨"cpus".toUTF8.data.toList, ⟨1530, 17, 0, 7, MycpuDecode.cpusAddress, 1024⟩⟩ := by decide

theorem executable_elf : Elf.read Images.kernel 16 2 = some 2 := by decide

end Xv6.Kernel.Symbols
