import MachCSL.Logic.IcacheCouplingSpec

namespace MachCSL.Logic.IcacheCoupling
open Iris Iris.Std Iris.CMRA Iris.BI

theorem count_elem_op i (q1 q2 : Qp) (v : Nat) :
    countElem i (q1 + q2) v = countElem i q1 v • countElem i q2 v := by
  unfold countElem
  rw [Heap.singleton_op_singleton (M := InumMap), ← DFracAgree.Frac.mk_op]

theorem count_elem_agree i q1 q2 (v1 v2 : Nat)
    (valid : ✓ (countElem i q1 v1 • countElem i q2 v2)) : v1 = v2 := by
  unfold countElem at valid
  rw [Heap.singleton_op_singleton (M := InumMap)] at valid
  exact DiscreteO.eqv_inj (DFracAgree.Frac.op_valid.mp ((Heap.singleton_valid_iff (M := InumMap)).mp valid)).2

theorem count_elem_update i (v1 v2 : Nat) :
    countElem i 1 v1 ~~> countElem i 1 v2 := by
  unfold countElem
  apply Heap.singleton_update (M := InumMap)
  unfold DFracAgree.Frac.mk
  apply Update.exclusive
  exact DFracAgree.mk_valid.mpr DFrac.valid_own_one

theorem mirror_elem_op i (q1 q2 : Qp) (v : Bool) :
    mirrorElem i (q1 + q2) v = mirrorElem i q1 v • mirrorElem i q2 v := by
  unfold mirrorElem
  rw [Heap.singleton_op_singleton (M := InumMap), ← DFracAgree.Frac.mk_op]

theorem mirror_elem_agree i q1 q2 (v1 v2 : Bool)
    (valid : ✓ (mirrorElem i q1 v1 • mirrorElem i q2 v2)) : v1 = v2 := by
  unfold mirrorElem at valid
  rw [Heap.singleton_op_singleton (M := InumMap)] at valid
  exact DiscreteO.eqv_inj (DFracAgree.Frac.op_valid.mp ((Heap.singleton_valid_iff (M := InumMap)).mp valid)).2

theorem mirror_elem_update i (v1 v2 : Bool) :
    mirrorElem i 1 v1 ~~> mirrorElem i 1 v2 := by
  unfold mirrorElem
  apply Heap.singleton_update (M := InumMap)
  unfold DFracAgree.Frac.mk
  apply Update.exclusive
  exact DFracAgree.mk_valid.mpr DFrac.valid_own_one

theorem pin_elem_op i (q1 q2 : Qp) (v : PinValue) :
    pinElem i (q1 + q2) v = pinElem i q1 v • pinElem i q2 v := by
  unfold pinElem
  rw [Heap.singleton_op_singleton (M := SlotMap), ← DFracAgree.Frac.mk_op]

theorem pin_elem_agree i q1 q2 (v1 v2 : PinValue)
    (valid : ✓ (pinElem i q1 v1 • pinElem i q2 v2)) : v1 = v2 := by
  unfold pinElem at valid
  rw [Heap.singleton_op_singleton (M := SlotMap)] at valid
  exact DiscreteO.eqv_inj (DFracAgree.Frac.op_valid.mp ((Heap.singleton_valid_iff (M := SlotMap)).mp valid)).2

theorem pin_elem_update i (v1 v2 : PinValue) :
    pinElem i 1 v1 ~~> pinElem i 1 v2 := by
  unfold pinElem
  apply Heap.singleton_update (M := SlotMap)
  unfold DFracAgree.Frac.mk
  apply Update.exclusive
  exact DFracAgree.mk_valid.mpr DFrac.valid_own_one

variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)

instance icnt_at_timeless i q v : Timeless (icnt_at capacity names i q v) := by
  unfold icnt_at; infer_instance
instance icnt_half_timeless i v : Timeless (icnt_half capacity names i v) := by
  unfold icnt_half; infer_instance
instance icnt_full_timeless i v : Timeless (icnt_full capacity names i v) := by
  unfold icnt_full; infer_instance

theorem count_fractional i q1 q2 v : icnt_at capacity names i (q1 + q2) v ⊣⊢
    icnt_at capacity names i q1 v ∗ icnt_at capacity names i q2 v := by
  unfold icnt_at
  rw [count_elem_op]
  exact iOwn_op (E := capacity.count)

theorem count_split i v : icnt_full capacity names i v ⊣⊢
    icnt_half capacity names i v ∗ icnt_half capacity names i v := by
  unfold icnt_full icnt_half
  simpa only [Qp.half_add_half] using count_fractional capacity names i (1 : Qp).half (1 : Qp).half v

theorem count_agree i v1 v2 : iprop(icnt_half capacity names i v1 ∗ icnt_half capacity names i v2 ⊢ ⌜v1 = v2⌝) := by
  unfold icnt_half icnt_at
  iintro ⟨H1, H2⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.count) $$ [$H1 $H2]
  ipureintro
  exact count_elem_agree i _ _ v1 v2 valid

theorem count_full_update i v1 v2 : iprop(icnt_full capacity names i v1 ⊢ |==> icnt_full capacity names i v2) := by
  unfold icnt_full icnt_at
  exact iOwn_update (E := capacity.count) (count_elem_update i v1 v2)

theorem count_update i v1 v2 : iprop(icnt_half capacity names i v1 ∗ icnt_half capacity names i v1 ⊢
    |==> (icnt_half capacity names i v2 ∗ icnt_half capacity names i v2)) := by
  rw [← (count_split capacity names i v1).to_eq, ← (count_split capacity names i v2).to_eq]
  exact count_full_update capacity names i v1 v2

theorem count_join i v : iprop(icnt_half capacity names i v ∗ icnt_half capacity names i v ⊢ icnt_full capacity names i v) :=
  (count_split capacity names i v).mpr

instance frzm_at_timeless i q v : Timeless (frzm_at capacity names i q v) := by
  unfold frzm_at; infer_instance
instance frzm_h_timeless i v : Timeless (frzm_h capacity names i v) := by
  unfold frzm_h; infer_instance
instance frzm_full_timeless i v : Timeless (frzm_full capacity names i v) := by
  unfold frzm_full; infer_instance

theorem mirror_fractional i q1 q2 v : frzm_at capacity names i (q1 + q2) v ⊣⊢
    frzm_at capacity names i q1 v ∗ frzm_at capacity names i q2 v := by
  unfold frzm_at
  rw [mirror_elem_op]
  exact iOwn_op (E := capacity.mirror)

theorem mirror_split i v : frzm_full capacity names i v ⊣⊢
    frzm_h capacity names i v ∗ frzm_h capacity names i v := by
  unfold frzm_full frzm_h
  simpa only [Qp.half_add_half] using mirror_fractional capacity names i (1 : Qp).half (1 : Qp).half v

theorem mirror_agree i v1 v2 : iprop(frzm_h capacity names i v1 ∗ frzm_h capacity names i v2 ⊢ ⌜v1 = v2⌝) := by
  unfold frzm_h frzm_at
  iintro ⟨H1, H2⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.mirror) $$ [$H1 $H2]
  ipureintro
  exact mirror_elem_agree i _ _ v1 v2 valid

theorem mirror_full_update i v1 v2 : iprop(frzm_full capacity names i v1 ⊢ |==> frzm_full capacity names i v2) := by
  unfold frzm_full frzm_at
  exact iOwn_update (E := capacity.mirror) (mirror_elem_update i v1 v2)

theorem mirror_update i v1 v2 : iprop(frzm_h capacity names i v1 ∗ frzm_h capacity names i v1 ⊢
    |==> (frzm_h capacity names i v2 ∗ frzm_h capacity names i v2)) := by
  rw [← (mirror_split capacity names i v1).to_eq, ← (mirror_split capacity names i v2).to_eq]
  exact mirror_full_update capacity names i v1 v2

theorem mirror_join i v : iprop(frzm_h capacity names i v ∗ frzm_h capacity names i v ⊢ frzm_full capacity names i v) :=
  (mirror_split capacity names i v).mpr

instance hpn_at_timeless i q v : Timeless (hpn_at capacity names i q v) := by
  unfold hpn_at; infer_instance
instance hpn_h_timeless i v : Timeless (hpn_h capacity names i v) := by
  unfold hpn_h; infer_instance
instance hpn_full_timeless i v : Timeless (hpn_full capacity names i v) := by
  unfold hpn_full; infer_instance

theorem pin_fractional i q1 q2 v : hpn_at capacity names i (q1 + q2) v ⊣⊢
    hpn_at capacity names i q1 v ∗ hpn_at capacity names i q2 v := by
  unfold hpn_at
  rw [pin_elem_op]
  exact iOwn_op (E := capacity.pin)

theorem pin_split i v : hpn_full capacity names i v ⊣⊢
    hpn_h capacity names i v ∗ hpn_h capacity names i v := by
  unfold hpn_full hpn_h
  simpa only [Qp.half_add_half] using pin_fractional capacity names i (1 : Qp).half (1 : Qp).half v

theorem pin_agree i v1 v2 : iprop(hpn_h capacity names i v1 ∗ hpn_h capacity names i v2 ⊢ ⌜v1 = v2⌝) := by
  unfold hpn_h hpn_at
  iintro ⟨H1, H2⟩
  ihave %valid := iOwn_cmraValid_op (E := capacity.pin) $$ [$H1 $H2]
  ipureintro
  exact pin_elem_agree i _ _ v1 v2 valid

theorem pin_full_update i v1 v2 : iprop(hpn_full capacity names i v1 ⊢ |==> hpn_full capacity names i v2) := by
  unfold hpn_full hpn_at
  exact iOwn_update (E := capacity.pin) (pin_elem_update i v1 v2)

theorem pin_update i v1 v2 : iprop(hpn_h capacity names i v1 ∗ hpn_h capacity names i v1 ⊢
    |==> (hpn_h capacity names i v2 ∗ hpn_h capacity names i v2)) := by
  rw [← (pin_split capacity names i v1).to_eq, ← (pin_split capacity names i v2).to_eq]
  exact pin_full_update capacity names i v1 v2

theorem pin_join i v : iprop(hpn_h capacity names i v ∗ hpn_h capacity names i v ⊢ hpn_full capacity names i v) :=
  (pin_split capacity names i v).mpr

end MachCSL.Logic.IcacheCoupling
