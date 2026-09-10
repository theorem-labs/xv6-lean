import Xv6.Elf.Representation
import Xv6.Elf.ImageRepresentation

/-!
Whole-parser correspondence between the packed file representation and its
contiguous byte list. The same fixed ELF64 layout functions receive either
reader; coverage proves those readers equal. This extends the correspondence to
header tables, PT_LOAD selection, structural checks, and image construction.
It does not prove equality with the original generated hex or Rocq kernel terms.
-/
namespace Xv6.Elf

def parseHeaderList (bytes : List UInt8) : Option Header :=
  parseHeaderWith (readList bytes)

def parseProgramHeaderList (bytes : List UInt8) (offset : Int) : Option ProgramHeader :=
  parseProgramHeaderWith (readList bytes) offset

def parseSectionHeaderList (bytes : List UInt8) (offset : Int) : Option SectionHeader :=
  parseSectionHeaderWith (readList bytes) offset

def programHeadersList (bytes : List UInt8) : Option (List ProgramHeader) := do
  let h ← parseHeaderList bytes
  table (parseProgramHeaderList bytes) h.phoff h.phentsize h.phnum.toNat

def sectionHeadersList (bytes : List UInt8) : Option (List SectionHeader) := do
  let h ← parseHeaderList bytes
  table (parseSectionHeaderList bytes) h.shoff h.shentsize h.shnum.toNat

/-- Like the source, malformed program-header tables have no load segments. -/
def loadsList (bytes : List UInt8) : List ProgramHeader :=
  match programHeadersList bytes with
  | none => []
  | some ps => ps.filter (·.type == 1)

def magicOKList (bytes : List UInt8) : Bool :=
  readList bytes 0 1 == some 0x7f && readList bytes 1 1 == some 0x45 &&
  readList bytes 2 1 == some 0x4c && readList bytes 3 1 == some 0x46 &&
  readList bytes 4 1 == some 2 && readList bytes 5 1 == some 1

def programHeaderWFList (bytes : List UInt8) (p : ProgramHeader) : Bool :=
  decide (0 ≤ p.offset) && decide (0 ≤ p.filesz) &&
  decide (p.offset + p.filesz ≤ (bytes.length : Int)) &&
  decide (p.filesz ≤ p.memsz) && decide (0 ≤ p.vaddr) &&
  decide (p.vaddr + p.memsz < 2 ^ 64)

def wellFormedList (bytes : List UInt8) : Bool :=
  match parseHeaderList bytes, programHeadersList bytes with
  | some h, some _ =>
    magicOKList bytes && (h.phentsize == 56) && decide (0 ≤ h.phoff) &&
    decide (0 ≤ h.phnum) &&
    decide (h.phoff + h.phnum * 56 ≤ (bytes.length : Int)) &&
    (loadsList bytes).all (programHeaderWFList bytes) && loadsDisjoint (loadsList bytes)
  | _, _ => false

def sectionsWellFormedList (bytes : List UInt8) : Bool :=
  match parseHeaderList bytes, sectionHeadersList bytes with
  | some h, some _ =>
    (h.shentsize == 64) && decide (0 ≤ h.shoff) && decide (0 ≤ h.shnum) &&
    decide (h.shoff + h.shnum * 64 ≤ (bytes.length : Int))
  | _, _ => false

private theorem read_function_eq (f : Image.Packed) (hc : f.Covered) :
    read f = readList f.toBytes :=
  funext fun offset => funext fun width => read_eq_readList f hc offset width

theorem parseHeader_eq_list (f : Image.Packed) (hc : f.Covered) :
    parseHeader f = parseHeaderList f.toBytes := by
  simp only [parseHeader, parseHeaderList, read_function_eq f hc]

theorem parseProgramHeader_eq_list (f : Image.Packed) (hc : f.Covered) (offset : Int) :
    parseProgramHeader f offset = parseProgramHeaderList f.toBytes offset := by
  simp only [parseProgramHeader, parseProgramHeaderList, read_function_eq f hc]

theorem parseSectionHeader_eq_list (f : Image.Packed) (hc : f.Covered) (offset : Int) :
    parseSectionHeader f offset = parseSectionHeaderList f.toBytes offset := by
  simp only [parseSectionHeader, parseSectionHeaderList, read_function_eq f hc]

/-- Equal field readers give equal ordered tables, including failed parses. -/
theorem table_congr {α : Type} (left right : Int → Option α)
    (h : ∀ offset, left offset = right offset) (offset step : Int) (count : Nat) :
    table left offset step count = table right offset step count :=
  congrArg (fun parse => table parse offset step count) (funext h)

theorem programHeaders_eq_list (f : Image.Packed) (hc : f.Covered) :
    programHeaders f = programHeadersList f.toBytes := by
  have hp : parseProgramHeader f = parseProgramHeaderList f.toBytes :=
    funext (parseProgramHeader_eq_list f hc)
  simp only [programHeaders, programHeadersList, parseHeader_eq_list f hc, hp]

theorem sectionHeaders_eq_list (f : Image.Packed) (hc : f.Covered) :
    sectionHeaders f = sectionHeadersList f.toBytes := by
  have hp : parseSectionHeader f = parseSectionHeaderList f.toBytes :=
    funext (parseSectionHeader_eq_list f hc)
  simp only [sectionHeaders, sectionHeadersList, parseHeader_eq_list f hc, hp]

theorem loads_eq_list (f : Image.Packed) (hc : f.Covered) :
    loads f = loadsList f.toBytes := by
  simp only [loads, loadsList, programHeaders_eq_list f hc]
  rfl

theorem magicOK_eq_list (f : Image.Packed) (hc : f.Covered) :
    magicOK f = magicOKList f.toBytes := by
  simp only [magicOK, magicOKList, read_eq_readList f hc]

theorem programHeaderWF_eq_list (f : Image.Packed) (p : ProgramHeader) :
    programHeaderWF f p = programHeaderWFList f.toBytes p := by
  simp only [programHeaderWF, programHeaderWFList, Image.Packed.toBytes_length]

theorem wellFormed_eq_list (f : Image.Packed) (hc : f.Covered) :
    wellFormed f = wellFormedList f.toBytes := by
  have hp : programHeaderWF f = programHeaderWFList f.toBytes :=
    funext (programHeaderWF_eq_list f)
  simp only [wellFormed, wellFormedList, parseHeader_eq_list f hc,
    programHeaders_eq_list f hc, magicOK_eq_list f hc, loads_eq_list f hc,
    Image.Packed.toBytes_length, hp]
  rfl

theorem sectionsWellFormed_eq_list (f : Image.Packed) (hc : f.Covered) :
    sectionsWellFormed f = sectionsWellFormedList f.toBytes := by
  simp only [sectionsWellFormed, sectionsWellFormedList, parseHeader_eq_list f hc,
    sectionHeaders_eq_list f hc, Image.Packed.toBytes_length]
  rfl

/-- Parsing and constructing the file-byte image both agree with the list model. -/
theorem fileImage_eq_parsed_list (f : Image.Packed) (hc : f.Covered) (address : Int) :
    fileImage f address = fileImageList f.toBytes (loadsList f.toBytes) address := by
  rw [fileImage_eq_list f hc, loads_eq_list f hc]

theorem zeroImage_eq_parsed_list (f : Image.Packed) (hc : f.Covered) (address : Int) :
    zeroImage f address = zeroImageList (loadsList f.toBytes) address := by
  rw [zeroImage_eq_list, loads_eq_list f hc]

/-- Full packed/list ELF image correspondence, including program-header parsing.
No well-formedness premise is required; malformed input behavior agrees too. -/
theorem loadedImage_eq_parsed_list (f : Image.Packed) (hc : f.Covered) (address : Int) :
    loadedImage f address = loadedImageList f.toBytes (loadsList f.toBytes) address := by
  rw [loadedImage_eq_list f hc, loads_eq_list f hc]

end Xv6.Elf
