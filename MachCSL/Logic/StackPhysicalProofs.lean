import MachCSL.Logic.StackPhysicalDefs
import MachCSL.Logic.TsoContextWordProofs

namespace MachCSL.Logic.StackPhysical
open Iris Iris.BI MachCSL.Memory MachCSL.Machine TsoContext
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem paStk_zero (sp : PhysicalAddress) : paStk sp 0 = sp := by simp [paStk]

theorem paStk_assoc (sp : PhysicalAddress) (a b : Nat) :
    paStk (paStk sp a) b = paStk sp (a + b) := by
  simp only [paStk, Nat.mul_add, BitVec.ofNat_add, BitVec.sub_sub]

theorem paStk_add_back (sp : PhysicalAddress) (n : Nat) :
    addressAdd (paStk sp n) (8 * n) = sp := by
  exact BitVec.sub_add_cancel sp (BitVec.ofNat 64 (8 * n))

theorem paStk_shift (sp : PhysicalAddress) (a i : Nat) :
    paStk sp (i + a + 1) = paStk (paStk sp a) (i + 1) := by
  rw [paStk_assoc]
  congr 1
  omega

/-- New sp+8 and new sp are exactly the source ra and s0 save slots. -/
theorem frame_two_addresses (sp : PhysicalAddress) :
    addressAdd (paStk sp 2) 8 = paStk sp 1 ∧
    addressAdd (paStk sp 2) 0 = paStk sp 2 := by
  constructor
  · have h := paStk_assoc sp 1 1
    change (sp - (8#64)) - (8#64) = sp - (16#64) at h
    change sp - (16#64) + (8#64) = sp - (8#64)
    rw [← h, BitVec.sub_add_cancel]
  · simp [addressAdd]

theorem words_append names ξ sp (left right : List TsoContextWord.Word) :
    iprop(words capacity names ξ sp (left ++ right) ⊣⊢
      words capacity names ξ sp left ∗
      words capacity names ξ (paStk sp left.length) right) := by
  unfold words
  rw [BigSepL.bigSepL_append.to_eq]
  simp only [paStk_shift]
  exact .rfl

theorem own_zero names ξ sp : iprop(own capacity names ξ sp 0 ⊣⊢ emp) := by
  refine ⟨Affine.affine, ?_⟩
  iintro Hemp
  unfold own
  iexists ([] : List TsoContextWord.Word)
  isplit
  · ipureintro
    rfl
  · unfold words
    rw [BigSepL.bigSepL_nil.to_eq]
    iexact Hemp

theorem own_append names ξ sp n₁ n₂ :
    iprop(own capacity names ξ sp (n₁ + n₂) ⊣⊢
      own capacity names ξ sp n₁ ∗ own capacity names ξ (paStk sp n₁) n₂) := by
  unfold own
  isplit
  · iintro ⟨%contents, %length, Hwords⟩
    have le : n₁ ≤ contents.length := by omega
    have htake : (contents.take n₁).length = n₁ := List.length_take_of_le le
    have hdrop : (contents.drop n₁).length = n₂ := by simp only [List.length_drop]; omega
    have split : contents = contents.take n₁ ++ contents.drop n₁ := (List.take_append_drop n₁ contents).symm
    rw [split, (words_append capacity names ξ sp _ _).to_eq, htake]
    icases Hwords with ⟨Htop, Hrest⟩
    isplitl [Htop]
    · iexists contents.take n₁
      iframe Htop
      ipureintro
      exact htake
    · iexists contents.drop n₁
      iframe Hrest
      ipureintro
      exact hdrop
  · iintro ⟨⟨%left, %hlen, Hleft⟩, ⟨%right, %hrlen, Hright⟩⟩
    iexists left ++ right
    isplit
    · ipureintro
      simp [hlen, hrlen]
    · rw [(words_append capacity names ξ sp left right).to_eq, hlen]
      iframe Hleft Hright

theorem own_split names ξ sp a n (bound : a ≤ n) :
    iprop(own capacity names ξ sp n ⊣⊢
      own capacity names ξ sp a ∗ own capacity names ξ (paStk sp a) (n - a)) := by
  have eq : n = a + (n - a) := by omega
  simpa only [← eq] using own_append capacity names ξ sp a (n - a)

theorem own_one names ξ sp :
    iprop(own capacity names ξ sp 1 ⊣⊢ ∃ word : TsoContextWord.Word,
      TsoContextWord.pointsto capacity names ξ (paStk sp 1) (.own 1) word) := by
  unfold own
  isplit
  · iintro ⟨%contents, %length, Hwords⟩
    obtain ⟨word, rfl⟩ := List.length_eq_one_iff.mp length
    iexists word
    unfold words
    rw [BigSepL.bigSepL_singleton.to_eq]
    iframe Hwords
  · iintro ⟨%word, Hword⟩
    iexists [word]
    isplit
    · ipureintro
      rfl
    · unfold words
      rw [BigSepL.bigSepL_singleton.to_eq]
      iframe Hword

theorem own_two names ξ sp :
    iprop(own capacity names ξ sp 2 ⊣⊢ ∃ first second : TsoContextWord.Word,
      TsoContextWord.pointsto capacity names ξ (paStk sp 1) (.own 1) first ∗
      TsoContextWord.pointsto capacity names ξ (paStk sp 2) (.own 1) second) := by
  rw [(own_append capacity names ξ sp 1 1).to_eq,
    (own_one capacity names ξ sp).to_eq,
    (own_one capacity names ξ (paStk sp 1)).to_eq, paStk_assoc]
  isplit
  · iintro ⟨⟨%first, Hfirst⟩, ⟨%second, Hsecond⟩⟩
    iexists first, second
    iframe Hfirst Hsecond
  · iintro ⟨%first, %second, Hfirst, Hsecond⟩
    isplitl [Hfirst]
    · iexists first
      iframe Hfirst
    · iexists second
      iframe Hsecond

/-- Exact two-slot save frame plus the untouched deeper stack. The saved
contents are existential: joining permits newly saved ra/s0 values. -/
theorem frame_two names ξ sp n (bound : 2 ≤ n) :
    iprop(own capacity names ξ sp n ⊣⊢ ∃ first second : TsoContextWord.Word,
      TsoContextWord.pointsto capacity names ξ (paStk sp 1) (.own 1) first ∗
      TsoContextWord.pointsto capacity names ξ (paStk sp 2) (.own 1) second ∗
      own capacity names ξ (paStk sp 2) (n - 2)) := by
  rw [(own_split capacity names ξ sp 2 n bound).to_eq, (own_two capacity names ξ sp).to_eq]
  isplit
  · iintro ⟨⟨%first, %second, Hfirst, Hsecond⟩, Hrest⟩
    iexists first, second
    iframe Hfirst Hsecond Hrest
  · iintro ⟨%first, %second, Hfirst, Hsecond, Hrest⟩
    iframe Hrest
    iexists first, second
    iframe Hfirst Hsecond

end MachCSL.Logic.StackPhysical
