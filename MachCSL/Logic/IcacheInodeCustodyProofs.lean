import MachCSL.Logic.IcacheInodeCustodySpec
import MachCSL.Logic.IcacheInodeCustodyPureProofs
import MachCSL.Logic.FsLinkProofs
import MachCSL.Logic.FsTopProofs
import Iris.ProofMode

namespace MachCSL.Logic.IcacheInodeCustody
open Iris Iris.Std Iris.BI Xv6.Fs
open Iris.Std.MultiSet Iris.Std.LawfulMultiSet Iris.Std.FiniteMultiSet

variable {GF : BundledGFunctors} (view : FsView.View GF)
    (links : FsLink.Capacity GF)

instance ireg_keep_timeless z v : Timeless (ireg_keep view links z v) := by
  unfold ireg_keep; split <;> infer_instance
instance ireg_lnk_at_timeless z n ty : Timeless (ireg_lnk_at view links z n ty) := by
  unfold ireg_lnk_at; infer_instance
instance ireg_lnk_timeless z d : Timeless (ireg_lnk view links z d) := by
  unfold ireg_lnk; infer_instance

theorem ireg_lnk_of_at z n ty d (hn : n = ireg_nl d) (ht : ty = d.typeZ) :
    iprop(ireg_lnk_at view links z n ty ⊢ ireg_lnk view links z d) := by
  subst n; subst ty; exact .rfl

theorem ireg_lnk_stable z d d' (hn : d'.nlinkZ = d.nlinkZ) (ht : d'.typeZ = d.typeZ) :
    iprop(ireg_lnk view links z d ⊢ ireg_lnk view links z d') := by
  have same : ireg_nl d' = ireg_nl d := by
    change (d'.nlink.toNat : Int) = d.nlink.toNat at hn
    change d'.nlink.toNat = d.nlink.toNat
    omega
  unfold ireg_lnk
  rw [same, ht]

theorem ireg_lnk_free_retype z d d' (hn : d.nlinkZ = 0) (hn' : d'.nlinkZ = 0) :
    iprop(ireg_lnk view links z d ⊢ ireg_lnk view links z d') := by
  change iprop((∃ v, ⌜ireg_reg_ok d.typeZ v⌝ ∗ FsLink.auth links view.link z (ireg_mult d) v ∗
    ireg_keep view links z v) ⊢ ∃ v, ⌜ireg_reg_ok d'.typeZ v⌝ ∗
    FsLink.auth links view.link z (ireg_mult d') v ∗ ireg_keep view links z v)
  rw [ireg_mult_zero d hn, ireg_mult_zero d' hn']
  obtain ⟨v', hv'⟩ := ireg_reg_ok_ex d'.typeZ
  unfold ireg_keep
  by_cases hz : z = 1
  · subst z
    simp only [↓reduceIte]
    iintro ⟨%v, _, Ha, Hk⟩
    ihave Hfalse := FsLink.auth_zero_no_tok links view.link 1 v v $$ Ha Hk
    icases Hfalse with ⟨⟩
  · simp only [hz, ↓reduceIte]
    iintro ⟨%v, _, Ha, _⟩
    iexists v'
    isplitr [Ha]
    · ipureintro; exact hv'
    · ihave Ha' := (FsLink.auth_zero_retype links view.link z v v').mp $$ Ha
      iframe

theorem ireg_lnk_bump z d d' k (hm : ireg_mult d' = ireg_mult d + k)
    (ht : d'.typeZ = d.typeZ) :
    iprop(⊢ ireg_lnk view links z d ==∗ ireg_lnk view links z d' ∗
      ∃ v, ⌜ireg_reg_ok d.typeZ v⌝ ∗ FsLink.toks links view.link z (FsLink.reps k v)) := by
  unfold ireg_lnk ireg_lnk_at
  iintro ⟨%v, %hv, Ha, Hk⟩
  imod FsLink.mint_reps links view.link z (ireg_mult_at (ireg_nl d) d.typeZ) k v $$ Ha with ⟨Ha, Ht⟩
  imodintro
  isplitl [Ha Hk]
  · iexists v
    isplitr [Ha Hk]
    · ipureintro; simpa only [ht] using hv
    · have hm' : ireg_mult_at (ireg_nl d') d'.typeZ = ireg_mult_at (ireg_nl d) d.typeZ + k := hm
      rw [hm']
      iframe
  · iexists v
    iframe
    ipureintro; exact hv

theorem ireg_lnk_fill z d d' v k (hz : ireg_mult d = 0) (hm : ireg_mult d' = k)
    (hv : ireg_reg_ok d'.typeZ v) :
    iprop(⊢ ireg_lnk view links z d ==∗ ireg_lnk view links z d' ∗
      FsLink.toks links view.link z (FsLink.reps k v)) := by
  change iprop(⊢ (∃ v0, ⌜ireg_reg_ok d.typeZ v0⌝ ∗
    FsLink.auth links view.link z (ireg_mult d) v0 ∗ ireg_keep view links z v0) ==∗
    (∃ v0, ⌜ireg_reg_ok d'.typeZ v0⌝ ∗ FsLink.auth links view.link z (ireg_mult d') v0 ∗
      ireg_keep view links z v0) ∗ FsLink.toks links view.link z (FsLink.reps k v))
  rw [hz, hm]
  unfold ireg_keep
  by_cases root : z = 1
  · subst z
    simp only [↓reduceIte]
    iintro ⟨%v0, _, Ha, Hk⟩
    ihave Hfalse := FsLink.auth_zero_no_tok links view.link 1 v0 v0 $$ Ha Hk
    icases Hfalse with ⟨⟩
  · simp only [root, ↓reduceIte]
    iintro ⟨%v0, _, Ha, _⟩
    ihave Ha := (FsLink.auth_zero_retype links view.link z v0 v).mp $$ Ha
    imod FsLink.mint_reps links view.link z 0 k v $$ Ha with ⟨Ha, Ht⟩
    imodintro
    isplitl [Ha]
    · iexists v
      isplitr [Ha]
      · ipureintro; exact hv
      · have zero : 0 + k = k := Nat.zero_add k
        isimp only [zero] at Ha
        iframe
    · iexact Ht

theorem ireg_lnk_drop z d d' v k (hm : ireg_mult d = ireg_mult d' + k)
    (ht : d'.typeZ = d.typeZ) :
    iprop(⊢ ireg_lnk view links z d -∗ FsLink.toks links view.link z (FsLink.reps k v) ==∗
      ireg_lnk view links z d') := by
  change iprop(⊢ (∃ v0, ⌜ireg_reg_ok d.typeZ v0⌝ ∗
    FsLink.auth links view.link z (ireg_mult d) v0 ∗ ireg_keep view links z v0) -∗
    FsLink.toks links view.link z (FsLink.reps k v) ==∗
    ∃ v0, ⌜ireg_reg_ok d'.typeZ v0⌝ ∗ FsLink.auth links view.link z (ireg_mult d') v0 ∗
      ireg_keep view links z v0)
  rw [hm]
  iintro ⟨%v0, %hv, Ha, Hk⟩ Ht
  imod FsLink.return_reps links view.link z (ireg_mult d') k v0 v $$ Ha Ht with Ha
  imodintro
  iexists v0
  iframe
  ipureintro; simpa only [ht] using hv

theorem ireg_lnk_toks_le z d pile :
    iprop(⊢ ireg_lnk view links z d -∗ FsLink.toks links view.link z pile -∗
      ⌜size pile ≤ ireg_mult d⌝) := by
  unfold ireg_lnk ireg_lnk_at
  iintro ⟨%v, _, Ha, _⟩ Ht
  ihave %h := FsLink.auth_toks_le links view.link z (ireg_mult_at (ireg_nl d) d.typeZ) v pile $$ Ha Ht
  ipureintro; exact h.1

theorem ireg_lnk_tok_nz z d v :
    iprop(⊢ ireg_lnk view links z d -∗ FsLink.tok links view.link z v -∗ ⌜d.nlinkZ ≠ 0⌝) := by
  iintro Hl Ht
  iunfold FsLink.tok at Ht
  ihave %h := ireg_lnk_toks_le view links z d ({v} : FsLink.Pile) $$ Hl Ht
  ipureintro
  intro hz
  rw [ireg_mult_zero d hz, size_singleton] at h
  omega

theorem ireg_lnk_tok_ty z d v :
    iprop(⊢ ireg_lnk view links z d -∗ FsLink.tok links view.link z v -∗ ⌜ireg_reg_ok d.typeZ v⌝) := by
  unfold ireg_lnk ireg_lnk_at
  iintro ⟨%v0, %hv, Ha, _⟩ Ht
  ihave %h := FsLink.auth_tok_agree links view.link z (ireg_mult_at (ireg_nl d) d.typeZ) v0 v $$ Ha Ht
  ipureintro
  simpa only [h.1] using hv

theorem ireg_lnk_toks_agree z d v v' :
    iprop(⊢ ireg_lnk view links z d -∗ FsLink.tok links view.link z v -∗
      FsLink.tok links view.link z v' -∗ ⌜v = v'⌝) := by
  unfold ireg_lnk ireg_lnk_at
  iintro ⟨%v0, _, Ha, _⟩ Ht Ht'
  ihave %h := FsLink.auth_tok_agree links view.link z (ireg_mult_at (ireg_nl d) d.typeZ) v0 v $$ Ha Ht
  ihave %h' := FsLink.auth_tok_agree links view.link z (ireg_mult_at (ireg_nl d) d.typeZ) v0 v' $$ Ha Ht'
  ipureintro; exact h.1.trans h'.1.symm

theorem ireg_lnk_root_alive d : iprop(ireg_lnk view links 1 d ⊢ ⌜1 ≤ d.nlinkZ⌝) := by
  unfold ireg_lnk ireg_lnk_at ireg_keep
  simp only [↓reduceIte]
  iintro ⟨%v, _, Ha, Ht⟩
  ihave %h := FsLink.auth_tok_agree links view.link 1 (ireg_mult_at (ireg_nl d) d.typeZ) v v $$ Ha Ht
  ipureintro
  have bound : 1 ≤ ireg_mult d := h.2
  by_cases hz : d.nlinkZ = 0
  · have hm := ireg_mult_zero d hz
    omega
  · change (d.nlink.toNat : Int) ≠ 0 at hz
    change 1 ≤ (d.nlink.toNat : Int)
    omega

theorem ireg_lnk_root_le z d k v :
    iprop(⊢ ireg_lnk view links z d -∗ FsLink.toks links view.link z (FsLink.reps k v) -∗
      ⌜z = 1 → (k : Int) ≤ d.nlinkZ⌝) := by
  unfold ireg_lnk ireg_lnk_at ireg_keep
  by_cases hz : z = 1
  · subst z
    simp only [↓reduceIte]
    iintro ⟨%v0, _, Ha, Hkeep⟩ Ht
    iunfold FsLink.tok at Hkeep
    ihave Htks := (FsLink.toks_split links view.link 1 ({v0} : FsLink.Pile) (FsLink.reps k v)).mpr $$ [$Hkeep $Ht]
    ihave %h := FsLink.auth_toks_le links view.link 1 (ireg_mult_at (ireg_nl d) d.typeZ) v0 _ $$ Ha Htks
    ipureintro
    intro _
    have hm := (ireg_mult_nl d).2
    rw [size_disjUnion, size_singleton, FsLink.reps_size] at h
    have bound : 1 + k ≤ ireg_mult d := h.1
    change ireg_mult d ≤ d.nlink.toNat + 1 at hm
    change (k : Int) ≤ (d.nlink.toNat : Int)
    omega
  · iintro _ _
    ipureintro
    intro h
    exact (hz h).elim

variable (tops : FsTop.Capacity GF)

instance ireg_top_park_timeless z d : Timeless (ireg_top_park view tops z d) := by
  unfold ireg_top_park; infer_instance

theorem ireg_top_park_nz z d n (h : d.typeZ ≠ 0) :
    iprop(FsTop.topFrag tops view z n ⊢ ireg_top_park view tops z d) := by
  unfold ireg_top_park
  iintro H
  iexists n
  iframe
  ipureintro
  intro bad
  exact (h bad).elim

theorem ireg_top_park_free z d (h : ireg_bare d) :
    iprop(FsTop.topFrag tops view z (freeNode d) ⊢ ireg_top_park view tops z d) := by
  unfold ireg_top_park
  iintro H
  iexists freeNode d
  iframe
  ipureintro
  intro _
  exact ⟨h, rfl⟩

theorem ireg_top_park_open z d (h : d.typeZ = 0) :
    iprop(ireg_top_park view tops z d ⊢ ⌜ireg_bare d⌝ ∗ FsTop.topFrag tops view z (freeNode d)) := by
  unfold ireg_top_park
  iintro ⟨%n, %hn, H⟩
  obtain ⟨hb, rfl⟩ := hn h
  iframe
  ipureintro; exact hb

theorem actual : Spec links tops where
  retype := fun view z d d' => ireg_lnk_free_retype view links z d d'
  bump := fun view z d d' k => ireg_lnk_bump view links z d d' k
  drop := fun view z d d' v k => ireg_lnk_drop view links z d d' v k
  root := fun view d => ireg_lnk_root_alive view links d
  topOpen := fun view z d => ireg_top_park_open view tops z d

end MachCSL.Logic.IcacheInodeCustody
