import Xv6.Elf.Defs

/-! ELF64 symbol-table readers. Field layout follows the System V gABI,
https://gabi.xinuos.com/elf/05-symtab.html and 03-sheader.html.
Names are raw bytes; no Unicode decoding or external nm result is trusted. -/
namespace Xv6.Elf

structure SymbolSection where
  header : SectionHeader
  link : Int
  entrySize : Int
  deriving DecidableEq, Repr

structure SymbolEntry where
  nameOffset : Int
  info : Int
  other : Int
  sectionIndex : Int
  value : Int
  size : Int
  deriving DecidableEq, Repr

structure NamedSymbol where
  name : List UInt8
  entry : SymbolEntry
  deriving DecidableEq, Repr

def parseSymbolSection (f : Image.Packed) (offset : Int) : Option SymbolSection := do
  let header ← parseSectionHeader f offset
  let link ← read f (offset + 40) 4
  let entrySize ← read f (offset + 56) 8
  pure ⟨header, link, entrySize⟩

def parseSymbolEntry (f : Image.Packed) (offset : Int) : Option SymbolEntry := do
  let name ← read f offset 4
  let info ← read f (offset + 4) 1
  let other ← read f (offset + 5) 1
  let sectionIndex ← read f (offset + 6) 2
  let value ← read f (offset + 8) 8
  let size ← read f (offset + 16) 8
  pure ⟨name, info, other, sectionIndex, value, size⟩

/-- A missing byte or missing terminator fails. Fuel is the remaining string
table extent, so a name cannot borrow a terminator outside its table. -/
def readCString (f : Image.Packed) (offset : Nat) : Nat → Option (List UInt8)
  | 0 => none
  | fuel + 1 => do
    let byte ← f.getByte? offset
    if byte == 0 then pure []
    else (byte :: ·) <$> readCString f (offset + 1) fuel

def sectionInFile (f : Image.Packed) (s : SectionHeader) : Bool :=
  decide (0 ≤ s.offset ∧ 0 ≤ s.size ∧ s.offset + s.size ≤ (f.byteLength : Int))

/-- Parse one actual symbol by table and row indices, following sh_link to its
string table. Extended section indices are retained raw, not resolved here. -/
def symbolAt (f : Image.Packed) (tableIndex rowIndex : Nat) : Option NamedSymbol := do
  let header ← parseHeader f
  if !magicOK f || header.shentsize != 64 || header.shoff < 0 ||
      (tableIndex : Int) ≥ header.shnum then none else do
    let table ← parseSymbolSection f (header.shoff + (tableIndex : Int) * 64)
    if table.header.type != 2 || table.entrySize != 24 ||
        table.header.flags / 2048 % 2 != 0 ||
        !sectionInFile f table.header || table.header.size % 24 != 0 ||
        (rowIndex : Int) * 24 ≥ table.header.size ||
        table.link < 0 || table.link ≥ header.shnum then none else do
      let strings ← parseSymbolSection f (header.shoff + table.link * 64)
      if strings.header.type != 3 || strings.header.flags / 2048 % 2 != 0 ||
          !sectionInFile f strings.header then none else do
        let entry ← parseSymbolEntry f (table.header.offset + (rowIndex : Int) * 24)
        if entry.nameOffset < 0 || entry.nameOffset ≥ strings.header.size then none else do
          let name ← readCString f (strings.header.offset + entry.nameOffset).toNat
            (strings.header.size - entry.nameOffset).toNat
          pure ⟨name, entry⟩

end Xv6.Elf
