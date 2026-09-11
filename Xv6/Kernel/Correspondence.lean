import Xv6.Kernel.Maps
import Xv6.Generated.KernelMapsCertificates
import Lean.Util.CollectAxioms

/-! Complete file-byte correspondence to the parsed actual ELF. The source importer
is untrusted; all equalities in this module are checked by Lean's kernel.
Authorship note: researched and written by OpenAI Codex on Jason Gross's behalf.
-/
namespace Xv6.Kernel
open Generated.KernelMaps

theorem code_eq_source_entries : code = listMap codeEntries := by
  funext a; exact runMap_eq_listMap codeRuns a

theorem data_eq_source_entries : data = listMap dataEntries := by
  funext a; exact runMap_eq_listMap dataRuns a

private theorem all_agree : ∀ run ∈ (codeRuns ++ dataRuns), ∀ a b,
    run.lookup a = some b → Elf.fileImage Images.kernel a = some b := by
  intro run hm a b hb
  simp only [Kernel.codeRuns, Kernel.dataRuns, Generated.KernelMaps.codeRuns,
    Generated.KernelMaps.dataRuns, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 <;> subst run
  · exact codeRun0_agrees a b hb
  · exact codeRun1_agrees a b hb
  · exact codeRun2_agrees a b hb
  · exact codeRun3_agrees a b hb
  · exact codeRun4_agrees a b hb
  · exact codeRun5_agrees a b hb
  · exact codeRun6_agrees a b hb
  · exact dataRun0_agrees a b hb
  · exact dataRun1_agrees a b hb
  · exact dataRun2_agrees a b hb
  · exact dataRun3_agrees a b hb
  · exact dataRun4_agrees a b hb
  · exact dataRun5_agrees a b hb

private theorem all_domain (a : Int) :
    (∃ run ∈ (codeRuns ++ dataRuns), run.base ≤ a ∧ a < run.base + run.length) ↔
      (0x80000000 ≤ a ∧ a < 0x8000a2a0) := by
  simp only [Kernel.codeRuns, Kernel.dataRuns, Generated.KernelMaps.codeRuns,
    Generated.KernelMaps.dataRuns, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  simp only [codeRun0, codeRun1, codeRun2, codeRun3, codeRun4, codeRun5, codeRun6, dataRun0, dataRun1, dataRun2, dataRun3, dataRun4, dataRun5]
  omega

/-- Exact equality of all 41632 source-imported file bytes, including absent addresses. -/
theorem fileBytes_eq_fileImage : fileBytes = Elf.fileImage Images.kernel := by
  rw [← runMap_eq_kernel_fileImage (codeRuns ++ dataRuns) all_agree all_domain]
  funext a
  exact (runMap_append codeRuns dataRuns a).symm

/-- Add precisely the parsed BSS zero tail to obtain the complete loaded ELF image. -/
theorem fileBytes_union_bss : Elf.union fileBytes (Elf.zeroImage Images.kernel) =
    Elf.loadedImage Images.kernel := by
  rw [fileBytes_eq_fileImage]
  funext a
  simp only [Elf.fileImage, Elf.zeroImage, Elf.loadedImage, Elf.Kernel.load_segments,
    Elf.segmentsUnion, List.foldr_cons, List.foldr_nil, Elf.segment, Elf.union]
  simp

/-- A source code byte is an actual loaded ELF byte. -/
theorem code_loaded (a : Int) (b : UInt8) (h : code a = some b) :
    Elf.loadedImage Images.kernel a = some b := by
  rw [← fileBytes_union_bss]
  apply Elf.union_left
  apply Elf.union_left
  exact h

/-- The source code map includes fetch padding but leaves the large text holes absent. -/
theorem code_defined_iff (a : Int) : (∃ b, code a = some b) ↔
    (0x80000000 ≤ a ∧ a < 0x80005ba0) ∨ (0x80006000 ≤ a ∧ a < 0x80006124) := by
  change (∃ b, runMap Kernel.codeRuns a = some b) ↔ _
  rw [runMap_defined_iff]
  simp only [Kernel.codeRuns, Generated.KernelMaps.codeRuns, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    codeRun0, codeRun1, codeRun2, codeRun3, codeRun4, codeRun5, codeRun6]
  omega

theorem data_defined_iff (a : Int) : (∃ b, data a = some b) ↔
    (0x80005ba0 ≤ a ∧ a < 0x80006000) ∨ (0x80006124 ≤ a ∧ a < 0x8000a2a0) := by
  change (∃ b, runMap Kernel.dataRuns a = some b) ↔ _
  rw [runMap_defined_iff]
  simp only [Kernel.dataRuns, Generated.KernelMaps.dataRuns, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    dataRun0, dataRun1, dataRun2, dataRun3, dataRun4, dataRun5]
  omega

theorem code_data_disjoint (a : Int) (c d : UInt8)
    (hc : code a = some c) (hd : data a = some d) : False := by
  have := (code_defined_iff a).mp ⟨c, hc⟩
  have := (data_defined_iff a).mp ⟨d, hd⟩
  omega

theorem data_loaded (a : Int) (b : UInt8) (h : data a = some b) :
    Elf.loadedImage Images.kernel a = some b := by
  rw [← fileBytes_union_bss]
  apply Elf.union_left
  cases hc : code a with
  | none => simp [fileBytes, Elf.union, hc, h]
  | some c => exact (code_data_disjoint a c b hc h).elim

/-- Addresses outside the file-backed interval, including BSS, are absent from
the combined source map. -/
theorem fileBytes_outside (a : Int) (h : a < memoryBase ∨ 0x8000a2a0 ≤ a) :
    fileBytes a = none := by
  rw [fileBytes_eq_fileImage, kernel_fileImage]
  have : ¬ (0x80000000 ≤ a ∧ a < 0x8000a2a0) := by
    change a < 0x80000000 ∨ 0x8000a2a0 ≤ a at h
    omega
  rw [if_neg this]

end Xv6.Kernel
