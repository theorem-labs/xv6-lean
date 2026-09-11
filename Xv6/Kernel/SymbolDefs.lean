import Xv6.Elf.SymbolDefs
import Xv6.Kernel.Maps

namespace Xv6.Kernel.Symbols

/-- A concrete imported symbol has its original ELF name, value and a defined
section index at this actual table row. This does not implement nm filtering. -/
def check (f : Image.Packed) (table row : Nat) (expected : Kernel.Symbol) : Bool :=
  (Elf.symbolAt f table row).any fun actual =>
    actual.name == expected.elfName.toUTF8.data.toList &&
    actual.entry.value == expected.address && actual.entry.sectionIndex != 0

end Xv6.Kernel.Symbols
