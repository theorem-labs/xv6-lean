import Xv6.Elf.Image
import Xv6.Elf.Kernel

namespace Xv6.Elf.Kernel

/-- Every byte of the actual kernel's BSS has zero value in the ELF image. -/
theorem bss {address : Int}
    (h : 0x80000000 + 41632 ≤ address ∧ address < 0x80000000 + 144840) :
    loadedImage Images.kernel address = some 0 := by
  simp only [loadedImage, load_segments, segmentsUnion, List.foldr_cons, List.foldr_nil]
  apply union_left
  exact segment_bss _ _ _ (by decide) h

end Xv6.Elf.Kernel
