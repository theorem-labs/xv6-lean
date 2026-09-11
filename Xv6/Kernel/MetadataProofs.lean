import Xv6.Kernel.Maps
import Xv6.Elf.Kernel

/-! Numeric metadata correspondence. Section names and symbol names are retained
from the source dump; this does not parse or certify the ELF string/symbol tables.
Authorship note: researched and written by OpenAI Codex on Jason Gross's behalf.
-/
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Xv6.Kernel

/-- Source entry metadata is the actual parsed ELF entry point. -/
theorem entry_parsed : (Elf.parseHeader Images.kernel).map Elf.Header.entry = some entry := by
  rw [Elf.Kernel.header]
  rfl

/-- Source segment metadata retains program-header order and all four dumped fields. -/
theorem segments_parsed : segments = (Elf.loads Images.kernel).map
    (fun p => (⟨p.vaddr, p.filesz, p.memsz, p.flags⟩ : Segment)) := by
  rw [Elf.Kernel.load_segments]
  rfl

/-- Numeric allocated-section metadata agrees with the real section-header parser.
The flags remain section flags; the program header is RWX. -/
theorem sections_parsed :
    sections.map (fun s => (s.address, s.endAddress - s.address, (s.flags : Int), s.hasFileContents)) =
    (((Elf.sectionHeaders Images.kernel).getD []).filter (fun s => s.flags % 4 ≥ 2)).map
      (fun s => (s.addr, s.size, s.flags, s.type != 8)) := by decide

theorem rodata_boundary : rodataEnd = 0x8000a264 := rfl

theorem writable_boundary :
    ((sections.filter (fun s => s.flags % 2 = 1)).head?).map Section.address = some rodataEnd := by
  decide

theorem segment_extent : segments = [⟨memoryBase, 41632, memoryEnd - memoryBase, 7⟩] := by decide

theorem symbol_count : symbols.length = 222 := by decide

theorem instruction_count : Generated.KernelMaps.instructionEntries.length = 8607 := by
  simp only [Generated.KernelMaps.instructionEntries, List.length_flatten, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  decide

end Xv6.Kernel
