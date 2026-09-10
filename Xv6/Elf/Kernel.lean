import Xv6.Elf.Proofs
import Xv6.Images

/-! Facts checked by Lean's kernel about the actual imported paper ELF.
These establish structural parsing; the loaded-memory correspondence is pending. -/
set_option maxRecDepth 4000
set_option maxHeartbeats 400000

namespace Xv6.Elf.Kernel

theorem header : parseHeader Images.kernel =
    some ⟨0x80000000, 64, 56, 3, 284216, 64, 21, 20⟩ := by decide

theorem load_segments : loads Images.kernel =
    [⟨1, 7, 4096, 0x80000000, 0x80000000, 41632, 144840, 4096⟩] := by decide

theorem loadable : wellFormed Images.kernel = true := by decide

theorem section_table_valid : sectionsWellFormed Images.kernel = true := by decide

/-- The parser genuinely distinguishes malformed inputs from this ELF. -/
theorem empty_rejected : wellFormed ⟨0, []⟩ = false := by decide

end Xv6.Elf.Kernel
