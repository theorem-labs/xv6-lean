import Xv6.Elf.Defs
import Lean.Elab.Tactic.Omega

namespace Xv6.Elf

theorem read_negative (f : Image.Packed) {offset : Int} (h : offset < 0)
    (width : Nat) : read f offset width = none := by
  simp [read, h]

theorem read_empty (f : Image.Packed) {offset : Int} (h : 0 ≤ offset) :
    read f offset 0 = some 0 := by
  simp [read, show ¬ offset < 0 by omega]

/-- Table parsing preserves its requested entry count, including empty tables. -/
theorem table_length {α : Type} (parse : Int → Option α) (step : Int)
    (n : Nat) (offset : Int) (entries : List α)
    (h : table parse offset step n = some entries) : entries.length = n := by
  induction n generalizing offset entries with
  | zero => simpa [table] using h.symm
  | succ n ih =>
    simp only [table] at h
    cases hp : parse offset with
    | none => simp [hp] at h
    | some a =>
      cases ht : table parse (offset + step) step n with
      | none => simp [hp, ht] at h
      | some rest =>
        simp [hp, ht] at h
        subst entries
        simpa using ih (offset + step) rest ht

theorem programHeaderWF_spec (f : Image.Packed) (p : ProgramHeader) :
    programHeaderWF f p = true ↔
      0 ≤ p.offset ∧ 0 ≤ p.filesz ∧
      p.offset + p.filesz ≤ (f.byteLength : Int) ∧
      p.filesz ≤ p.memsz ∧ 0 ≤ p.vaddr ∧ p.vaddr + p.memsz < 2 ^ 64 := by
  simp [programHeaderWF, and_assoc]

/-- Disjointness excludes a byte from belonging to both loaded ranges. -/
theorem rangesDisjoint_excludes (p q : ProgramHeader) (a : Int)
    (hd : rangesDisjoint p q = true)
    (hp : p.vaddr ≤ a ∧ a < p.vaddr + p.memsz)
    (hq : q.vaddr ≤ a ∧ a < q.vaddr + q.memsz) : False := by
  simp [rangesDisjoint] at hd
  omega

end Xv6.Elf
