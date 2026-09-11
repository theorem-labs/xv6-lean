import MachCSL.Logic.LogTxDefs

namespace MachCSL.Logic.LogTx
open Iris Iris.Std Iris.BI

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  noOps : ∀ name t q, iprop(⊢ auth capacity name ∅ -∗ tx_pin capacity name t q -∗ False)
  optionalNoOps : ∀ name pin,
    iprop(⊢ auth capacity name ∅ -∗ tx_pin_o capacity name pin -∗ ⌜pin = none⌝)
  ledgerNoOps : ∀ (K : Type) (M : Type → Type) [LawfulFiniteMap M K] name (pins : M (Nat × Qp)),
    iprop(⊢ auth capacity name ∅ -∗ tx_pins capacity name pins -∗ ⌜pins = ∅⌝)
  split : ∀ name t q q1 q2, q = q1 + q2 →
    iprop(tx_pin capacity name t q ⊣⊢ tx_pin capacity name t q1 ∗ tx_pin capacity name t q2)
  allocate : ∀ frame : IProp GF,
    iprop(frame ⊢ |==> ∃ name, auth capacity name ∅ ∗ frame)
  insert : ∀ name transactions t, transactions[t]? = none →
    iprop(⊢ auth capacity name transactions ==∗
      auth capacity name (PartialMap.insert transactions t ()) ∗ tx_pin capacity name t 1)
  delete : ∀ name transactions t,
    iprop(⊢ auth capacity name transactions -∗ tx_pin capacity name t 1 ==∗
      auth capacity name (PartialMap.delete transactions t))

end MachCSL.Logic.LogTx
