import MachCSL.Logic.TsoViewsSpec

/-! Source `TsoGhost.v` monotone view and log-length receipt laws. -/
namespace MachCSL.Logic.Tso.Views
open MachCSL.Memory Iris Iris.Algebra Iris.CMRA Iris.BI Auth
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance natLB_persistent γ n : Persistent (natLB capacity γ n) := by
  letI := capacity.monoNat γ
  infer_instance
instance natLB_timeless γ n : Timeless (natLB capacity γ n) := by
  letI := capacity.monoNat γ
  infer_instance
instance natAuth_timeless γ dq n : Timeless (natAuth capacity γ dq n) := by
  letI := capacity.monoNat γ
  infer_instance
instance llb_persistent γ n : Persistent (llb capacity γ n) := by
  unfold llb; infer_instance
instance llb_timeless γ n : Timeless (llb capacity γ n) := by
  unfold llb; infer_instance
instance viewFrag_persistent γ h n : Persistent (viewFrag capacity γ h n) := by
  unfold viewFrag; infer_instance
instance viewFrag_timeless γ h n : Timeless (viewFrag capacity γ h n) := by
  unfold viewFrag; infer_instance
instance viewAuth_timeless γ vs : Timeless (viewAuth capacity γ vs) := by
  unfold viewAuth; infer_instance
instance viewLB_persistent γv γll h n : Persistent (viewLB capacity γv γll h n) := by
  unfold viewLB; infer_instance
instance viewLB_timeless γv γll h n : Timeless (viewLB capacity γv γll h n) := by
  unfold viewLB; infer_instance

theorem natLB_le γ n lower (le : lower ≤ n) :
    iprop(⊢ natLB capacity γ n -∗ natLB capacity γ lower) := by
  letI := capacity.monoNat γ
  exact MonoNat.lb_own_le γ (.ofNat n) (.ofNat lower) le

theorem natLB_get γ dq n :
    iprop(⊢ natAuth capacity γ dq n -∗ natLB capacity γ n) := by
  letI := capacity.monoNat γ
  exact MonoNat.lb_own_get γ dq (.ofNat n)

theorem natLB_valid γ dq n bound :
    iprop(⊢ natAuth capacity γ dq n -∗ natLB capacity γ bound -∗ ⌜bound ≤ n⌝) := by
  letI := capacity.monoNat γ
  iintro Ha Hl
  ihave %hv := MonoNat.auth_lb_own_valid γ dq (.ofNat n) (.ofNat bound) $$ Ha Hl
  ipureintro
  exact hv.2

/-- One slot supports independently allocated log-length and generation names. -/
theorem natAuth_alloc (n : Nat) :
    iprop(⊢ |==> ∃ γ, natAuth capacity γ (.own 1) n ∗ natLB capacity γ n) := by
  letI := capacity.monoNat 0
  exact MonoNat.own_alloc (.ofNat n)

theorem natAuth_update γ n n' (le : n ≤ n') :
    iprop(⊢ natAuth capacity γ (.own 1) n ==∗
      natAuth capacity γ (.own 1) n' ∗ natLB capacity γ n') := by
  letI := capacity.monoNat γ
  exact MonoNat.own_update γ (.ofNat n) (.ofNat n') le

theorem llb_zero γ : iprop(⊢ llb capacity γ 0) := by
  unfold llb
  iright
  ipureintro
  rfl

theorem llb_le γ bound lower (le : lower ≤ bound) :
    iprop(⊢ llb capacity γ bound -∗ llb capacity γ lower) := by
  unfold llb
  iintro H
  icases H with (H | %hz)
  · ileft
    iapply natLB_le capacity γ bound lower le $$ H
  · iright
    ipureintro
    omega

theorem llb_max γ a b :
    iprop(⊢ llb capacity γ a -∗ llb capacity γ b -∗ llb capacity γ (max a b)) := by
  by_cases h : a ≤ b
  · rw [Nat.max_eq_right h]
    iintro _ H
    iexact H
  · rw [Nat.max_eq_left (by omega : b ≤ a)]
    iintro H _
    iexact H

theorem llb_get γ dq n :
    iprop(⊢ natAuth capacity γ dq n -∗ natAuth capacity γ dq n ∗ llb capacity γ n) := by
  iintro H
  ihave #Hl := natLB_get capacity γ dq n $$ H
  iframe H
  unfold llb
  ileft
  iexact Hl

theorem llb_valid γ dq n bound :
    iprop(⊢ natAuth capacity γ dq n -∗ llb capacity γ bound -∗ ⌜bound ≤ n⌝) := by
  unfold llb
  iintro Ha Hl
  icases Hl with (Hl | %hz)
  · iapply natLB_valid capacity γ dq n bound $$ Ha Hl
  · ipureintro
    omega

theorem viewLB_zero γv γll h : iprop(⊢ viewLB capacity γv γll h 0) := by
  unfold viewLB
  iright
  ipureintro
  rfl

theorem viewLB_llb γv γll h bound :
    iprop(⊢ viewLB capacity γv γll h bound -∗ llb capacity γll bound) := by
  unfold viewLB llb
  iintro H
  icases H with (⟨_, Hl⟩ | %hz)
  · ileft
    iexact Hl
  · iright
    ipureintro
    exact hz

theorem viewFrag_le γ h bound lower (le : lower ≤ bound) :
    iprop(⊢ viewFrag capacity γ h bound -∗ viewFrag capacity γ h lower) := by
  unfold viewFrag
  iintro H
  iapply (iOwn_mono (E := capacity.views)) $$ H
  exact Auth.frag_inc_of_inc (vone_le_incl h bound lower le)

theorem viewLB_le γv γll h bound lower (le : lower ≤ bound) :
    iprop(⊢ viewLB capacity γv γll h bound -∗ viewLB capacity γv γll h lower) := by
  unfold viewLB
  iintro H
  icases H with (⟨Hv, Hl⟩ | %hz)
  · ileft
    ihave Hv' := viewFrag_le capacity γv h bound lower le $$ Hv
    ihave Hl' := natLB_le capacity γll bound lower le $$ Hl
    iframe
  · iright
    ipureintro
    omega

theorem viewAuth_alloc (views : Agent → Nat) :
    iprop(⊢ |==> ∃ γ, viewAuth capacity γ views) := by
  unfold viewAuth
  apply iOwn_alloc (E := capacity.views)
  exact Auth.auth_both_valid_2 (vf_valid views) (inc_refl _)

theorem viewAuth_frag γ views h bound (le : bound ≤ views h) :
    iprop(⊢ viewAuth capacity γ views -∗ viewFrag capacity γ h bound) := by
  unfold viewAuth viewFrag
  iintro H
  iapply (iOwn_mono (E := capacity.views)) $$ H
  exact Auth.frag_included.mpr (vone_incl_vf h bound views le)

theorem viewAuth_update γ views views' (le : ∀ h, views h ≤ views' h) :
    iprop(⊢ viewAuth capacity γ views ==∗ viewAuth capacity γ views') := by
  unfold viewAuth
  iintro H
  iapply (iOwn_update (E := capacity.views)) $$ H
  exact Auth.auth_update (vf_local_update views views' le)

/-- The authority bounds a fragment at its exact Nat agent coordinate. -/
theorem viewFrag_valid γ views h bound :
    iprop(⊢ viewAuth capacity γ views -∗ viewFrag capacity γ h bound -∗
      ⌜bound ≤ views h⌝) := by
  unfold viewAuth viewFrag
  iintro Ha Hf
  icases (iOwn_cmraValid_op (E := capacity.views)) $$ [$Ha $Hf] with %hv
  ipureintro
  rw [← CMRA.assoc, ← Auth.frag_op] at hv
  have hi := (Auth.auth_both_valid_discrete.mp hv).1
  have hh := MaxNat.inc_iff.mp (DiscreteFun.inc_apply hi h)
  change max (views h) (if h = h then bound else 0) ≤ views h at hh
  simp only [ite_true] at hh
  omega

theorem viewAuth_valid γv γll views h bound :
    iprop(⊢ viewAuth capacity γv views -∗ viewLB capacity γv γll h bound -∗
      ⌜bound ≤ views h⌝) := by
  unfold viewLB
  iintro Ha Hl
  icases Hl with (⟨Hf, _⟩ | %hz)
  · iapply viewFrag_valid capacity γv views h bound $$ Ha Hf
  · ipureintro
    omega

theorem viewLB_get γv γll views h n (le : views h ≤ n) :
    iprop(⊢ viewAuth capacity γv views -∗ natAuth capacity γll (.own 1) n -∗
      viewAuth capacity γv views ∗ natAuth capacity γll (.own 1) n ∗
        viewLB capacity γv γll h (views h)) := by
  iintro Hv Hn
  ihave #Hf := viewAuth_frag capacity γv views h (views h) (Nat.le_refl _) $$ Hv
  ihave #Hl := natLB_get capacity γll (.own 1) n $$ Hn
  ihave #Hl' := natLB_le capacity γll n (views h) le $$ Hl
  iframe Hv Hn
  unfold viewLB
  ileft
  iframe Hf Hl'

/-- Checked implementation of the separately importable client contract. -/
theorem viewsSpec : ViewsSpec capacity where
  alloc := viewAuth_alloc capacity
  update := viewAuth_update capacity
  zero := viewLB_zero capacity
  weaken := viewLB_le capacity
  logBound := viewLB_llb capacity
  valid := viewAuth_valid capacity
  get := viewLB_get capacity
  logValid := llb_valid capacity

/-- The extension supplies this contract without any extra resource assumptions. -/
theorem registryViewsSpec : ViewsSpec registryCapacity := viewsSpec registryCapacity

end MachCSL.Logic.Tso.Views
