import MachCSL.Logic.LogTxSpec

namespace MachCSL.Logic.LogTx
open Iris Iris.Std Iris.Algebra Iris.BI
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance auth_timeless name transactions : Timeless (auth capacity name transactions) := by
  letI := capacity.transactions
  unfold auth authQ
  infer_instance
instance tx_pin_timeless name t q : Timeless (tx_pin capacity name t q) := by
  letI := capacity.transactions
  unfold tx_pin
  infer_instance
instance tx_pin_o_timeless name pin : Timeless (tx_pin_o capacity name pin) := by
  cases pin <;> unfold tx_pin_o <;> infer_instance
instance tx_pins_timeless {K : Type} {M : Type → Type} [LawfulFiniteMap M K]
    name (pins : M (Nat × Qp)) : Timeless (tx_pins capacity name pins) := by
  unfold tx_pins
  infer_instance

theorem lookup name dq transactions t q :
    iprop(⊢ authQ capacity name dq transactions -∗ tx_pin capacity name t q -∗
      ⌜transactions[t]? = some ()⌝) := by
  letI := capacity.transactions
  exact ghost_map_lookup

theorem tx_pin_no_ops name t q :
    iprop(⊢ auth capacity name ∅ -∗ tx_pin capacity name t q -∗ False) := by
  iintro Ha Hp
  iunfold auth at Ha
  ihave %found := lookup capacity name (.own 1) ∅ t q $$ Ha Hp
  simp at found

theorem tx_pin_o_no_ops name pin :
    iprop(⊢ auth capacity name ∅ -∗ tx_pin_o capacity name pin -∗ ⌜pin = none⌝) := by
  iintro Ha Hp
  cases pin with
  | none => ipureintro; rfl
  | some pin =>
    iunfold tx_pin_o at Hp
    ihave %bad := tx_pin_no_ops capacity name pin.1 pin.2 $$ Ha Hp
    exact bad.elim

theorem tx_pins_no_ops {K : Type} {M : Type → Type} [LawfulFiniteMap M K]
    name (pins : M (Nat × Qp)) :
    iprop(⊢ auth capacity name ∅ -∗ tx_pins capacity name pins -∗ ⌜pins = ∅⌝) := by
  iintro Ha Hpins
  ihave %empty : ⌜∀ key : K, get? pins key = none⌝ $$ [Ha Hpins]
  · iapply pure_forall.mpr
    iintro %key
    cases found : get? pins key with
    | none => ipureintro; rfl
    | some pin =>
      iunfold tx_pins at Hpins
      ihave Hp := BigSepM.bigSepM_lookup found $$ Hpins
      ihave %bad := tx_pin_no_ops capacity name pin.1 pin.2 $$ Ha Hp
      exact bad.elim
  · ipureintro
    apply LawfulPartialMap.equiv_iff_eq.mp
    intro key
    rw [empty key, LawfulPartialMap.get?_empty]

theorem tx_pin_split_iff name t q q1 q2 (sum : q = q1 + q2) :
    iprop(tx_pin capacity name t q ⊣⊢ tx_pin capacity name t q1 ∗ tx_pin capacity name t q2) := by
  letI := capacity.transactions
  subst q
  exact Fractional.fractional (Φ := fun q : Qp =>
    (ghost_map_elem name (.own q) t () : IProp GF)) q1 q2

theorem tx_pin_split name t q q1 q2 (sum : q = q1 + q2) :
    iprop(tx_pin capacity name t q ⊢ tx_pin capacity name t q1 ∗ tx_pin capacity name t q2) :=
  (tx_pin_split_iff capacity name t q q1 q2 sum).mp

theorem tx_pin_join_q name t q q1 q2 (sum : q = q1 + q2) :
    iprop(⊢ tx_pin capacity name t q1 -∗ tx_pin capacity name t q2 -∗ tx_pin capacity name t q) := by
  iintro H1 H2
  iapply (tx_pin_split_iff capacity name t q q1 q2 sum).mpr
  iframe H1 H2

theorem allocate_empty (frame : IProp GF) :
    iprop(frame ⊢ |==> ∃ name, auth capacity name ∅ ∗ frame) := by
  letI := capacity.transactions
  iintro HR
  imod (ghost_map_alloc_empty (H := TxMap) (K := Nat) (V := Unit)) with ⟨%name, Ha⟩
  imodintro
  iexists name
  unfold auth authQ
  iframe HR Ha

theorem insert name transactions t (fresh : transactions[t]? = none) :
    iprop(⊢ auth capacity name transactions ==∗
      auth capacity name (PartialMap.insert transactions t ()) ∗ tx_pin capacity name t 1) := by
  letI := capacity.transactions
  exact ghost_map_insert t () fresh

theorem delete name transactions t :
    iprop(⊢ auth capacity name transactions -∗ tx_pin capacity name t 1 ==∗
      auth capacity name (PartialMap.delete transactions t)) := by
  letI := capacity.transactions
  exact ghost_map_delete t ()

theorem tx_pin_elem name t q :
    tx_pin capacity name t q =
      (letI := capacity.transactions
       ghost_map_elem (H := TxMap) name (.own q) t () : IProp GF) := rfl

instance log_tx_timeless name : Timeless (log_tx capacity name) := by
  unfold log_tx
  infer_instance

open scoped Classical in
/-- Source begin_op transaction mint, with the id hidden in its returned token. -/
theorem mint name (transactions : TxMap Unit) :
    iprop(auth capacity name transactions ⊢ |==> ∃ t,
      ⌜transactions[t]? = none⌝ ∗
      auth capacity name (PartialMap.insert transactions t ()) ∗ log_tx capacity name) := by
  let t : Nat := Iris.Std.Heap.fresh (M := TxMap) (m := transactions) True.intro
  have fresh : transactions[t]? = none :=
    Iris.Std.Heap.get?_fresh (M := TxMap) (m := transactions) (H := True.intro)
  iintro Ha
  imod insert capacity name transactions t fresh $$ Ha with ⟨Ha, Ht⟩
  imodintro
  iexists t
  iframe Ha
  isplit
  · ipureintro; exact fresh
  · unfold log_tx
    iexists t
    iexact Ht

/-- Source end_op retires the full token's own row, with no invented tie to
an independently indexed operation-budget entry. -/
theorem retire name (transactions : TxMap Unit) :
    iprop(⊢ auth capacity name transactions -∗ log_tx capacity name ==∗ ∃ t,
      ⌜transactions[t]? = some ()⌝ ∗ auth capacity name (PartialMap.delete transactions t)) := by
  iintro Ha Ht
  iunfold log_tx at Ht
  icases Ht with ⟨%t, Ht⟩
  have look : iprop(⊢ auth capacity name transactions -∗ tx_pin capacity name t 1 -∗
      ⌜transactions[t]? = some ()⌝) := lookup capacity name (.own 1) transactions t 1
  ihave %found := look $$ Ha Ht
  imod delete capacity name transactions t $$ Ha Ht with Ha
  imodintro
  iexists t
  iframe Ha
  ipureintro
  exact found

/-- The source commit reads only the cardinality tie at an empty operation map. -/
theorem empty_of_ops {V : Type} (transactions : TxMap Unit) (operations : TxMap V)
    (sameSize : transactions.size = operations.size) (empty : operations = ∅) : transactions = ∅ := by
  apply _root_.Std.ExtTreeMap.eq_empty_iff_size_eq_zero.mpr
  simpa [empty] using sameSize

theorem actual : Spec capacity :=
  ⟨tx_pin_no_ops capacity, tx_pin_o_no_ops capacity,
    fun _ _ _ => tx_pins_no_ops capacity, tx_pin_split_iff capacity,
    allocate_empty capacity, insert capacity, delete capacity⟩

end MachCSL.Logic.LogTx
