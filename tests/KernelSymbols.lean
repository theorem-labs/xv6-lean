import Xv6.Elf.SymbolDefs

/-! Independent regressions for the selected uncompressed ELF64 row reader.
This synthetic 512-byte fixture is not a full well-formed ELF object: only the
fields consumed by symbolAt are populated. Offset/width pairs follow gABI
Elf64_Shdr and Elf64_Sym. No upstream binary or generator output is trusted.

Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.
-/
namespace Tests.KernelSymbols
open Xv6 Xv6.Elf
set_option exponentiation.threshold 4096
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Replace a small little-endian field, keeping the other bytes. -/
def patch (page : Nat) (offset width value : Nat) : Nat :=
  page % 2^(8*offset) + value * 2^(8*offset) +
    (page / 2^(8*(offset+width))) * 2^(8*(offset+width))

def fields : List (Nat × Nat × Nat) :=
  [ (0, 6, 0x0102464c457f), -- magic, ELF64, little-endian
    (40, 8, 64), (58, 2, 64), (60, 2, 3), -- section table
    (132, 4, 2), (152, 8, 256), (160, 8, 48), (168, 4, 2), (184, 8, 24), -- symtab
    (196, 4, 3), (216, 8, 304), (224, 8, 5), -- linked strtab
    (280, 4, 1), (284, 1, 0x12), (286, 2, 1), -- row 1
    (288, 8, 0x800018ba), (296, 8, 32),
    (304, 5, 0x626100) ] -- NUL, a, b, NUL, NUL

def setFields (page : Nat) (changes : List (Nat × Nat × Nat)) : Nat :=
  changes.foldl (fun page (offset, width, value) => patch page offset width value) page

def fixture (changes : List (Nat × Nat × Nat) := []) : Image.Packed :=
  ⟨512, [setFields (setFields 0 fields) changes]⟩

def good : NamedSymbol := ⟨[97,98], ⟨1, 0x12, 0, 1, 0x800018ba, 32⟩⟩

example : symbolAt fixture 1 1 = some good := by decide
-- String offsets may point to a suffix, not only to the start after a NUL.
example : symbolAt (fixture [(280,4,2)]) 1 1 =
    some { good with name := [98], entry := { good.entry with nameOffset := 2 } } := by decide
example : symbolAt (fixture [(280,4,0)]) 1 1 =
    some { good with name := [], entry := { good.entry with nameOffset := 0 } } := by decide
-- A terminator immediately outside the declared string extent is unavailable.
example : symbolAt (fixture [(224,8,3)]) 1 1 = none := by decide
example : symbolAt fixture 1 2 = none := by decide
example : symbolAt (fixture [(168,4,3)]) 1 1 = none := by decide
example : symbolAt (fixture [(196,4,2)]) 1 1 = none := by decide
example : symbolAt (fixture [(160,8,47)]) 1 1 = none := by decide
example : symbolAt (fixture [(184,8,25)]) 1 1 = none := by decide
example : symbolAt (fixture [(152,8,500)]) 1 1 = none := by decide
example : symbolAt (fixture [(0,1,0)]) 1 1 = none := by decide
-- SHF_COMPRESSED changes the payload format of either selected section.
example : symbolAt (fixture [(136,8,2048)]) 1 1 = none := by decide
example : symbolAt (fixture [(200,8,2048)]) 1 1 = none := by decide
example : symbolAt (⟨512, []⟩ : Image.Packed) 1 1 = none := by decide
-- Deliberate scope: selected row access does not validate an unused table tail.
example : symbolAt (fixture [(60,2,999)]) 1 1 = some good := by decide

end Tests.KernelSymbols
