import Xv6.Kernel.KernelStackSpec
import Xv6.Kernel.KernelDatumWordLink
import MachCSL.Logic.StackPhysicalProofs

namespace Xv6.Kernel.KernelStack
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic
open StackPhysical (paStk_assoc paStk_shift)
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem words_append era tier ξ sp (left right : List TsoContextWord.Word) :
    iprop(words capacity era tier ξ sp (left ++ right) ⊣⊢
      words capacity era tier ξ sp left ∗
      words capacity era tier ξ (paStk sp left.length) right) := by
  unfold words
  rw [BigSepL.bigSepL_append.to_eq]
  simp only [paStk_shift]
  exact .rfl

theorem own_zero era tier ξ sp : iprop(own capacity era tier ξ sp 0 ⊣⊢ emp) := by
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

theorem own_append era tier ξ sp n₁ n₂ :
    iprop(own capacity era tier ξ sp (n₁ + n₂) ⊣⊢
      own capacity era tier ξ sp n₁ ∗ own capacity era tier ξ (paStk sp n₁) n₂) := by
  unfold own
  isplit
  · iintro ⟨%contents, %length, Hwords⟩
    have le : n₁ ≤ contents.length := by omega
    have htake : (contents.take n₁).length = n₁ := List.length_take_of_le le
    have hdrop : (contents.drop n₁).length = n₂ := by simp only [List.length_drop]; omega
    have split : contents = contents.take n₁ ++ contents.drop n₁ := (List.take_append_drop n₁ contents).symm
    rw [split, (words_append capacity era tier ξ sp _ _).to_eq, htake]
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
    · rw [(words_append capacity era tier ξ sp left right).to_eq, hlen]
      iframe Hleft Hright

theorem own_split era tier ξ sp a n (bound : a ≤ n) :
    iprop(own capacity era tier ξ sp n ⊣⊢
      own capacity era tier ξ sp a ∗ own capacity era tier ξ (paStk sp a) (n - a)) := by
  have eq : n = a + (n - a) := by omega
  simpa only [← eq] using own_append capacity era tier ξ sp a (n - a)

theorem own_one era tier ξ sp :
    iprop(own capacity era tier ξ sp 1 ⊣⊢ ∃ word : TsoContextWord.Word,
      KernelDatum.word capacity era tier ξ (paStk sp 1) (.own 1) word) := by
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

theorem own_two era tier ξ sp :
    iprop(own capacity era tier ξ sp 2 ⊣⊢ ∃ first second : TsoContextWord.Word,
      KernelDatum.word capacity era tier ξ (paStk sp 1) (.own 1) first ∗
      KernelDatum.word capacity era tier ξ (paStk sp 2) (.own 1) second) := by
  rw [(own_append capacity era tier ξ sp 1 1).to_eq,
    (own_one capacity era tier ξ sp).to_eq,
    (own_one capacity era tier ξ (paStk sp 1)).to_eq]
  have address : paStk (paStk sp 1) 1 = paStk sp 2 := StackPhysical.paStk_assoc sp 1 1
  rw [address]
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
theorem frame_two era tier ξ sp n (bound : 2 ≤ n) :
    iprop(own capacity era tier ξ sp n ⊣⊢ ∃ first second : TsoContextWord.Word,
      KernelDatum.word capacity era tier ξ (paStk sp 1) (.own 1) first ∗
      KernelDatum.word capacity era tier ξ (paStk sp 2) (.own 1) second ∗
      own capacity era tier ξ (paStk sp 2) (n - 2)) := by
  rw [(own_split capacity era tier ξ sp 2 n bound).to_eq, (own_two capacity era tier ξ sp).to_eq]
  isplit
  · iintro ⟨⟨%first, %second, Hfirst, Hsecond⟩, Hrest⟩
    iexists first, second
    iframe Hfirst Hsecond Hrest
  · iintro ⟨%first, %second, Hfirst, Hsecond, Hrest⟩
    iframe Hrest
    iexists first, second
    iframe Hfirst Hsecond

theorem mono era tier tier' ξ sp n (le : KernelDatum.Tier.Le tier tier') :
    iprop(own capacity era tier ξ sp n ⊢ own capacity era tier' ξ sp n) := by
  unfold own
  iintro ⟨%contents,%length,Hwords⟩
  iexists contents
  isplit
  · ipureintro; exact length
  unfold words
  iapply BigSepL.bigSepL_mono (fun {_ _} _ =>
    KernelDatum.word_mono capacity era tier tier' ξ _ (.own 1) _ le) $$ Hwords

theorem sp_bounds era tier ξ sp n (positive : 0 < n) :
    iprop(own capacity era tier ξ sp n ⊢ ⌜8 ≤ sp.toNat ∧ sp.toNat < 2^38 + 8⌝) := by
  iintro Hstack
  ihave ⟨Hone,_⟩ := (own_split capacity era tier ξ sp 1 n (by omega)).mp $$ Hstack
  ihave ⟨%value,Hword⟩ := (own_one capacity era tier ξ sp).mp $$ Hone
  ihave ⟨%ppn,Hclaim,_⟩ := KernelDatumWord.choose capacity era tier ξ (paStk sp 1) (.own 1) value $$ Hword
  iunfold KernelDatum.claim at Hclaim
  icases Hclaim with ⟨_,%facts⟩
  have first : (paStk sp 1).toNat < 2^38 := facts.1
  have size := sp.isLt
  simp only [paStk, StackPhysical.paStk, Nat.mul_one, BitVec.toNat_sub, BitVec.toNat_ofNat] at first
  ipureintro
  omega

theorem sp_nonzero era tier ξ sp n (positive : 0 < n) :
    iprop(own capacity era tier ξ sp n ⊢ ⌜sp ≠ 0#64⌝) := by
  iintro Hstack
  ihave %bounds := sp_bounds capacity era tier ξ sp n positive $$ Hstack
  ipureintro
  intro zero
  subst sp
  simp at bounds

theorem actual : Spec capacity :=
  ⟨own_zero capacity,own_append capacity,own_split capacity,own_one capacity,own_two capacity,
    frame_two capacity,mono capacity,sp_bounds capacity,sp_nonzero capacity⟩

end Xv6.Kernel.KernelStack
