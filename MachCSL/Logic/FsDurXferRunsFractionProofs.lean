import MachCSL.Logic.FsDurXferRunsSpec

namespace MachCSL.Logic.FsDurXferRuns
open Iris Iris.CMRA

theorem qp_no_pair_lt (q1 q2 : Qp) (h1 : 1 < q1 + q1) (h2 : 1 < q2 + q2)
    (sum : q1 + q2 ≤ 1) : False := by
  change (1 : Rat) < q1.val + q1.val at h1
  change (1 : Rat) < q2.val + q2.val at h2
  change q1.val + q2.val ≤ (1 : Rat) at sum
  grind

theorem qp_no_pair_le (q1 q2 : Qp) (h1 : 1 ≤ q1 + q1) (h2 : 1 ≤ q2 + q2)
    (sum : q1 + q2 < 1) : False := by
  change (1 : Rat) ≤ q1.val + q1.val at h1
  change (1 : Rat) ≤ q2.val + q2.val at h2
  change q1.val + q2.val < (1 : Rat) at sum
  grind

theorem dfrac_nvalid_shape (dq : DFrac) (invalid : ¬✓ (dq • dq)) :
    ∃ q : Qp, (dq = .own q ∧ 1 < q + q) ∨ (dq = .ownDiscard q ∧ 1 ≤ q + q) := by
  cases dq with
  | own q =>
    refine ⟨q, Or.inl ⟨rfl, ?_⟩⟩
    change ¬ q.val + q.val ≤ (1 : Rat) at invalid
    change (1 : Rat) < q.val + q.val
    grind
  | discard => exact False.elim (invalid trivial)
  | ownDiscard q =>
    refine ⟨q, Or.inr ⟨rfl, ?_⟩⟩
    change ¬ q.val + q.val < (1 : Rat) at invalid
    change (1 : Rat) ≤ q.val + q.val
    grind

theorem dfrac_nvalid_pair (dq1 dq2 : DFrac) (left : ¬✓ (dq1 • dq1)) (right : ¬✓ (dq2 • dq2)) :
    ¬✓ (dq1 • dq2) := by
  intro valid
  obtain ⟨q1, (⟨rfl, h1⟩ | ⟨rfl, h1⟩)⟩ := dfrac_nvalid_shape dq1 left
  all_goals obtain ⟨q2, (⟨rfl, h2⟩ | ⟨rfl, h2⟩)⟩ := dfrac_nvalid_shape dq2 right
  · exact qp_no_pair_lt q1 q2 h1 h2 valid
  · apply qp_no_pair_le q1 q2 (by change (1 : Rat) ≤ q1.val + q1.val; change (1 : Rat) < q1.val + q1.val at h1; grind) h2 valid
  · apply qp_no_pair_le q1 q2 h1 (by change (1 : Rat) ≤ q2.val + q2.val; change (1 : Rat) < q2.val + q2.val at h2; grind) valid
  · exact qp_no_pair_le q1 q2 h1 h2 valid

theorem dfrac_full_pair (dq : DFrac) : ¬✓ (DFrac.own 1 • dq) := FsView.dfrac_full_invalid dq

theorem qp_gt_half_double (q : Qp) (half : (1 : Qp).half < q) : 1 < q + q := by
  change (1 / 2 : Rat) < q.val at half
  change (1 : Rat) < q.val + q.val
  grind

theorem dfrac_own_gt_half (q : Qp) (half : (1 : Qp).half < q) : ¬✓ (DFrac.own q • DFrac.own q) := by
  have bound := qp_gt_half_double q half
  change (1 : Rat) < q.val + q.val at bound
  change ¬ q.val + q.val ≤ (1 : Rat)
  grind

theorem qp_half_lt_1 : (1 : Qp).half < 1 := by change (1 / 2 : Rat) < 1; grind
theorem qp_half_lt_34 : (1 : Qp).half < Qp.threeQuarters := by change (1 / 2 : Rat) < 3 / 4; grind

end MachCSL.Logic.FsDurXferRuns
