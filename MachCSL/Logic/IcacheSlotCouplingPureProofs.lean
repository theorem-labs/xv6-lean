import MachCSL.Logic.IcacheSlotCouplingDefs

namespace MachCSL.Logic.IcacheSlotCoupling
open Iris Xv6.Fs IcacheRefLedger

theorem fresh_shape_wf {d : Dinode} (h : fresh_shape d) : d.WellFormed := by
  simp [Dinode.WellFormed, h.2.2.1]
theorem fresh_shape_nlink {d : Dinode} (h : fresh_shape d) : d.nlink.toNat = 0 := h.2.2.2

theorem ireg_claim_ok_none (f : FreezeCell) (d : Dinode) : ireg_claim_ok none f d := trivial
theorem ireg_claim_ok_shape {c f d} (present : c ≠ none) (h : ireg_claim_ok c f d) : fresh_shape d := by
  cases c with
  | none => exact (present rfl).elim
  | some x => exact h.1
theorem ireg_claim_ok_off {c f d} (present : c ≠ none) (h : ireg_claim_ok c f d) : f = freezeCell .off := by
  cases c with
  | none => exact (present rfl).elim
  | some x => exact h.2.1
theorem ireg_claim_ok_ty {ty t q f d} (h : ireg_claim_ok (claimCell ty t q) f d) : d.type = ty := h.2.2.symm
theorem ireg_claim_ok_invalid (f : FreezeCell) (d : Dinode) : ¬ ireg_claim_ok (some .invalid) f d := fun h => h.2.2

theorem ireg_ref_ok_zero (n : Nat) (c : ClaimCell) (d : Dinode) : ireg_ref_ok 0 0 n c d :=
  ⟨Nat.zero_le _, fun _ => ⟨rfl,rfl⟩, fun _ => rfl⟩
theorem ireg_ref_ok_count0 {r rc n c d} (h : ireg_ref_ok r rc n c d) (zero : n = 0) : r = 0 ∧ rc = 0 := by
  have := h.1; omega
theorem ireg_ref_ok_ty0 {r rc n c d} (h : ireg_ref_ok r rc n c d) (zero : d.type.toNat = 0) : r = 0 ∧ rc = 0 := h.2.1 zero
theorem ireg_ref_ok_alloc {r rc n c d} (h : ireg_ref_ok r rc n c d) (positive : 1 ≤ r + rc) : d.type.toNat ≠ 0 := by
  intro zero; obtain ⟨hr,hc⟩ := h.2.1 zero; omega
theorem ireg_ref_ok_unclaimed {r rc n c d} (h : ireg_ref_ok r rc n c d) (positive : 1 ≤ r) : c = none := by
  by_cases eq : c = none
  · exact eq
  · have := h.2.2 eq; omega
theorem ireg_ref_ok_retire {r rc n c d} (h : ireg_ref_ok r (rc + 1) n c d) (nz : d.type.toNat ≠ 0) :
    ireg_ref_ok (r + 1) rc n none d := by
  exact ⟨by have := h.1; omega, fun eq => (nz eq).elim, fun ne => (ne rfl).elim⟩
theorem ireg_ref_ok_unclaim {r rc n c d} (h : ireg_ref_ok r rc n c d) : ireg_ref_ok r rc n none d :=
  ⟨h.1,h.2.1,fun ne => (ne rfl).elim⟩
theorem ireg_ref_ok_stable {r rc n c d d'} (same : d'.type = d.type) (h : ireg_ref_ok r rc n c d) : ireg_ref_ok r rc n c d' := by
  simpa only [ireg_ref_ok, same] using h
theorem ireg_ref_ok_claim_mint {r rc n d d'} (c' : ClaimCell) (h : ireg_ref_ok r rc n none d)
    (zero : d.type.toNat = 0) (nz : d'.type.toNat ≠ 0) : ireg_ref_ok r rc n c' d' := by
  obtain ⟨rfl,rfl⟩ := h.2.1 zero
  exact ireg_ref_ok_zero _ _ _
theorem ireg_ref_ok_mint {r rc n c d} (b : Bool) (h : ireg_ref_ok r rc n c d)
    (nz : d.type.toNat ≠ 0) (unclaimed : b = false → c = none) :
    ireg_ref_ok (rup b r) (rcup b rc) (n + 1) c d := by
  cases b <;> simp only [rup, rcup, Bool.false_eq_true, ↓reduceIte]
  · exact ⟨by have := h.1; omega, fun eq => (nz eq).elim, fun ne => (ne (unclaimed rfl)).elim⟩
  · exact ⟨by have := h.1; omega, fun eq => (nz eq).elim, h.2.2⟩
theorem ireg_ref_ok_spend {r rc n c d} (b : Bool)
    (h : ireg_ref_ok (rup b r) (rcup b rc) (n + 1) c d) : ireg_ref_ok r rc n c d := by
  cases b <;> simp only [rup, rcup, Bool.false_eq_true, ↓reduceIte, ireg_ref_ok] at h ⊢
  all_goals exact ⟨by omega, fun zero => by have := h.2.1 zero; omega, fun ne => by have := h.2.2 ne; omega⟩

theorem ireg_frzm_ok_false {f} (h : frz_preb f = false) : ireg_frzm_ok false f := h.symm
theorem ireg_frzm_ok_true (rg : FreezeIndex) : ireg_frzm_ok true (freezeCell (.pre rg)) := rfl

theorem ireg_frz_ok_off (n : Nat) (d : Dinode) : ireg_frz_ok (freezeCell .off) n d := trivial
theorem ireg_frz_ok_none (n : Nat) (d : Dinode) : ¬ ireg_frz_ok none n d := id
theorem ireg_frz_ok_invalid (n : Nat) (d : Dinode) : ¬ ireg_frz_ok (some .invalid) n d := id

theorem ireg_frz_ok_not_pre {f n d} (positive : 1 ≤ n) (notpre : frz_preb f = false)
    (h : ireg_frz_ok f n d) : f = freezeCell .off := by
  cases f with
  | none => exact h.elim
  | some x => cases x with
    | invalid => exact h.elim
    | excl phase => cases phase with | mk phase => cases phase with
      | off => rfl
      | pre rg => cases notpre
      | post rg => have := h.2.2; omega

theorem ireg_frz_ok_stable {f n d d'} (nl : d'.nlink = d.nlink) (ty : d'.type = d.type)
    (h : ireg_frz_ok f n d) : ireg_frz_ok f n d' := by
  unfold ireg_frz_ok at *
  split at h <;> simp_all only [nl, ty]

theorem ireg_frz_ok_nz {f n d} (nz : d.nlink.toNat ≠ 0) (h : ireg_frz_ok f n d) : f = freezeCell .off := by
  cases f with
  | none => exact h.elim
  | some x => cases x with
    | invalid => exact h.elim
    | excl phase => cases phase with | mk phase => cases phase with
      | off => rfl
      | pre rg => exact (nz h.1).elim
      | post rg => exact (nz h.1).elim

theorem ireg_frz_ok_ty0 {f n d} (zero : d.type.toNat = 0) (h : ireg_frz_ok f n d) : f = freezeCell .off := by
  cases f with
  | none => exact h.elim
  | some x => cases x with
    | invalid => exact h.elim
    | excl phase => cases phase with | mk phase => cases phase with
      | off => rfl
      | pre rg => exact (h.2.1 zero).elim
      | post rg => exact (h.2.1 zero).elim

theorem ireg_frz_ok_ge2 {f n d} (ge : 2 ≤ n) (h : ireg_frz_ok f n d) : f = freezeCell .off := by
  cases f with
  | none => exact h.elim
  | some x => cases x with
    | invalid => exact h.elim
    | excl phase => cases phase with | mk phase => cases phase with
      | off => rfl
      | pre rg => have := h.2.2; omega
      | post rg => have := h.2.2; omega

theorem ireg_frz_ok_of_off {f n d} (h : f = freezeCell .off) : ireg_frz_ok f n d := h ▸ ireg_frz_ok_off n d

theorem ireg_frz_ok_phase {ph ph' n n' d} (h : ireg_frz_ok (freezeCell ph) n d)
    (off : ph = .off → ph' = .off)
    (pre : ∀ rg, ph' = .pre rg → n' = 1) (post : ∀ rg, ph' = .post rg → n' = 0) :
    ireg_frz_ok (freezeCell ph') n' d := by
  cases ph' with
  | off => trivial
  | pre rg =>
    cases ph with
    | off => cases off rfl
    | pre old => exact ⟨h.1,h.2.1,pre rg rfl⟩
    | post old => exact ⟨h.1,h.2.1,pre rg rfl⟩
  | post rg =>
    cases ph with
    | off => cases off rfl
    | pre old => exact ⟨h.1,h.2.1,post rg rfl⟩
    | post old => exact ⟨h.1,h.2.1,post rg rfl⟩

end MachCSL.Logic.IcacheSlotCoupling
