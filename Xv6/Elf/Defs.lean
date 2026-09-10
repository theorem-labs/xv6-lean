import Xv6.Image.Packed

/-!
ELF64 readers and structural checks, following `iris/ElfFile.v` in xv6iris
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476 (readers, records, tables, and elf_wf).
Reads use partial packed access. Correspondence with the reference byte-list
representation requires its coverage/lookup bridge; it is not asserted here.
No segment loading or instruction semantics are defined in this file.
-/
namespace Xv6.Elf

def assembleLE : List UInt8 → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * assembleLE rest

/-- As in the reference, an empty read succeeds at any nonnegative offset. -/
def read (f : Image.Packed) (offset : Int) (width : Nat) : Option Int := do
  if offset < 0 then none
  else if width = 0 then some 0
  else
    let bytes ← (List.range width).mapM fun i => f.getByte? (offset.toNat + i)
    pure (Int.ofNat (assembleLE bytes))

structure Header where
  entry : Int
  phoff : Int
  phentsize : Int
  phnum : Int
  shoff : Int
  shentsize : Int
  shnum : Int
  shstrndx : Int
  deriving DecidableEq, Repr

structure ProgramHeader where
  type : Int
  flags : Int
  offset : Int
  vaddr : Int
  paddr : Int
  filesz : Int
  memsz : Int
  align : Int
  deriving DecidableEq, Repr

structure SectionHeader where
  name : Int
  type : Int
  flags : Int
  addr : Int
  offset : Int
  size : Int
  deriving DecidableEq, Repr

def parseHeaderWith (readAt : Int → Nat → Option Int) : Option Header := do
  let entry ← readAt 0x18 8
  let phoff ← readAt 0x20 8
  let shoff ← readAt 0x28 8
  let phentsize ← readAt 0x36 2
  let phnum ← readAt 0x38 2
  let shentsize ← readAt 0x3a 2
  let shnum ← readAt 0x3c 2
  let shstrndx ← readAt 0x3e 2
  pure ⟨entry, phoff, phentsize, phnum, shoff, shentsize, shnum, shstrndx⟩

def parseHeader (f : Image.Packed) : Option Header :=
  parseHeaderWith (read f)

def parseProgramHeaderWith (readAt : Int → Nat → Option Int) (o : Int) : Option ProgramHeader := do
  let type ← readAt o 4
  let flags ← readAt (o + 4) 4
  let offset ← readAt (o + 8) 8
  let vaddr ← readAt (o + 16) 8
  let paddr ← readAt (o + 24) 8
  let filesz ← readAt (o + 32) 8
  let memsz ← readAt (o + 40) 8
  let align ← readAt (o + 48) 8
  pure ⟨type, flags, offset, vaddr, paddr, filesz, memsz, align⟩

def parseProgramHeader (f : Image.Packed) (o : Int) : Option ProgramHeader :=
  parseProgramHeaderWith (read f) o

def parseSectionHeaderWith (readAt : Int → Nat → Option Int) (o : Int) : Option SectionHeader := do
  let name ← readAt o 4
  let type ← readAt (o + 4) 4
  let flags ← readAt (o + 8) 8
  let addr ← readAt (o + 16) 8
  let offset ← readAt (o + 24) 8
  let size ← readAt (o + 32) 8
  pure ⟨name, type, flags, addr, offset, size⟩

def parseSectionHeader (f : Image.Packed) (o : Int) : Option SectionHeader :=
  parseSectionHeaderWith (read f) o

def table {α : Type} (parse : Int → Option α) (offset step : Int) :
    Nat → Option (List α)
  | 0 => some []
  | n + 1 => do
    let a ← parse offset
    let rest ← table parse (offset + step) step n
    pure (a :: rest)

def programHeaders (f : Image.Packed) : Option (List ProgramHeader) := do
  let h ← parseHeader f
  table (parseProgramHeader f) h.phoff h.phentsize h.phnum.toNat

def sectionHeaders (f : Image.Packed) : Option (List SectionHeader) := do
  let h ← parseHeader f
  table (parseSectionHeader f) h.shoff h.shentsize h.shnum.toNat

/-- Malformed header tables have no load segments, as in `elf_loads`. -/
def loads (f : Image.Packed) : List ProgramHeader :=
  match programHeaders f with
  | none => []
  | some ps => ps.filter (·.type == 1)

def magicOK (f : Image.Packed) : Bool :=
  read f 0 1 == some 0x7f && read f 1 1 == some 0x45 &&
  read f 2 1 == some 0x4c && read f 3 1 == some 0x46 &&
  read f 4 1 == some 2 && read f 5 1 == some 1

def programHeaderWF (f : Image.Packed) (p : ProgramHeader) : Bool :=
  decide (0 ≤ p.offset) && decide (0 ≤ p.filesz) &&
  decide (p.offset + p.filesz ≤ (f.byteLength : Int)) &&
  decide (p.filesz ≤ p.memsz) && decide (0 ≤ p.vaddr) &&
  decide (p.vaddr + p.memsz < 2 ^ 64)

def rangesDisjoint (p q : ProgramHeader) : Bool :=
  decide (p.vaddr + p.memsz ≤ q.vaddr) ||
  decide (q.vaddr + q.memsz ≤ p.vaddr) ||
  decide (p.memsz ≤ 0) || decide (q.memsz ≤ 0)

def loadsDisjoint : List ProgramHeader → Bool
  | [] => true
  | p :: rest => rest.all (rangesDisjoint p) && loadsDisjoint rest

/-- Structural loadability predicate from `elf_wf`; not a loader theorem. -/
def wellFormed (f : Image.Packed) : Bool :=
  match parseHeader f, programHeaders f with
  | some h, some _ =>
    magicOK f && (h.phentsize == 56) && decide (0 ≤ h.phoff) &&
    decide (0 ≤ h.phnum) &&
    decide (h.phoff + h.phnum * 56 ≤ (f.byteLength : Int)) &&
    (loads f).all (programHeaderWF f) && loadsDisjoint (loads f)
  | _, _ => false

def sectionsWellFormed (f : Image.Packed) : Bool :=
  match parseHeader f, sectionHeaders f with
  | some h, some _ =>
    (h.shentsize == 64) && decide (0 ≤ h.shoff) && decide (0 ≤ h.shnum) &&
    decide (h.shoff + h.shnum * 64 ≤ (f.byteLength : Int))
  | _, _ => false

end Xv6.Elf
