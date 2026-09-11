import Xv6.Kernel.Proofs
import Xv6.Elf.ImageFacts

namespace Xv6.Kernel

/-- Closed form of the parsed file-backed image of the actual paper ELF. -/
theorem kernel_fileImage (a : Int) :
    Elf.fileImage Images.kernel a =
      if 0x80000000 ≤ a ∧ a < 0x8000a2a0 then
        Images.kernel.getByte? (4096 + (a - 0x80000000).toNat) else none := by
  simp only [Elf.fileImage, Elf.Kernel.load_segments, Elf.segmentsUnion,
    List.foldr_cons, List.foldr_nil, Elf.union, Elf.segmentFile]
  have hw : Elf.fileWindowLength Images.kernel
      ⟨1, 7, 4096, 0x80000000, 0x80000000, 41632, 144840, 4096⟩ = 41632 := by decide
  rw [hw]
  have hb : (0 ≤ a - 0x80000000 ∧ a - 0x80000000 < (41632 : Int)) ↔
      (0x80000000 ≤ a ∧ a < 0x8000a2a0) := by omega
  change ((if 0 ≤ a - 0x80000000 ∧ a - 0x80000000 < (41632 : Int) then
    Images.kernel.getByte? (4096 + (a - 0x80000000).toNat) else none).orElse (fun _ => none)) = _
  simp only [hb]
  split <;> simp

/-- A page certificate relates a source run to the parsed ELF image. -/
theorem ByteRun.agrees_fileImage (run : ByteRun) (page offset : Nat) (word : Nat)
    (hp : Images.kernel.pages[page]? = some word)
    (hw : offset + run.length ≤ 4096)
    (hb : page * 4096 + offset + run.length ≤ Images.kernel.byteLength)
    (hr : run.base = 0x80000000 + (page * 4096 + offset : Nat) - 4096)
    (hg : 0x80000000 ≤ run.base ∧ run.base + run.length ≤ 0x8000a2a0)
    (cert : run.payload = (word >>> (8 * offset)) % 2 ^ (8 * run.length))
    (a : Int) (b : UInt8) (h : run.lookup a = some b) :
    Elf.fileImage Images.kernel a = some b := by
  obtain ⟨hlo, hhi, hval⟩ := (run.lookup_some_iff a b).mp h
  have hi : (a - run.base).toNat < run.length := by omega
  have hs := run.slice_read Images.kernel page offset word hp hw hb cert _ hi
  have he : 4096 + (a - 0x80000000).toNat =
      page * 4096 + offset + (a - run.base).toNat := by omega
  rw [kernel_fileImage, if_pos (show 0x80000000 ≤ a ∧ a < 0x8000a2a0 from ⟨by omega, by omega⟩), he, hs, hval]

/-- Pointwise byte agreement plus exact domain coverage closes the sparse union.
No missing address is defaulted to zero. -/
theorem runMap_eq_kernel_fileImage (runs : List ByteRun)
    (agreement : ∀ run ∈ runs, ∀ a b, run.lookup a = some b → Elf.fileImage Images.kernel a = some b)
    (domain : ∀ a, (∃ run ∈ runs, run.base ≤ a ∧ a < run.base + run.length) ↔
      (0x80000000 ≤ a ∧ a < 0x8000a2a0)) :
    runMap runs = Elf.fileImage Images.kernel := by
  funext a
  cases he : runMap runs a with
  | some b =>
    obtain ⟨run, hm, hr⟩ := runMap_some_exists runs a b he
    exact (agreement run hm a b hr).symm
  | none =>
    have hnot : ¬(0x80000000 ≤ a ∧ a < 0x8000a2a0) := by
      intro hin
      have hd := (runMap_defined_iff runs a).mpr ((domain a).mpr hin)
      simp [he] at hd
    rw [kernel_fileImage, if_neg hnot]

end Xv6.Kernel
