import Iris.Instances.Lib.GhostMap
import Iris.Std.HeapInstances

/-! The actual source ln_tx camera and TxPin vocabulary. Names are explicit;
pins retain the lending transaction and its positive share. -/
namespace MachCSL.Logic.LogTx
open Iris Iris.Std Iris.Algebra Iris.BI

abbrev TxMap (V : Type) := _root_.Std.ExtTreeMap Nat V
abbrev TxRA := HeapView Nat (Agree (DiscreteO Unit)) TxMap
abbrev TxRF := constOF TxRA
def txFunctor : GFunctor := ⟨TxRF, inferInstance⟩
structure Capacity (GF : BundledGFunctors) where
  transactions : GhostMapG GF Nat Unit TxMap

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def authQ (name : GName) (dq : DFrac) (transactions : TxMap Unit) : IProp GF :=
  letI := capacity.transactions
  ghost_map_auth (H := TxMap) name dq transactions
def auth (name : GName) (transactions : TxMap Unit) : IProp GF :=
  authQ capacity name (.own 1) transactions
def tx_pin (name : GName) (transaction : Nat) (share : Qp) : IProp GF :=
  letI := capacity.transactions
  ghost_map_elem name (.own share) transaction ()
/-- Source log_tx intentionally forgets the transaction identifier. -/
def log_tx (name : GName) : IProp GF := iprop(∃ transaction : Nat, tx_pin capacity name transaction 1)
def tx_pin_o (name : GName) (pin : Option (Nat × Qp)) : IProp GF :=
  match pin with
  | none => emp
  | some (transaction, share) => tx_pin capacity name transaction share
def tx_pins {K : Type} {M : Type → Type} [LawfulFiniteMap M K]
    (name : GName) (pins : M (Nat × Qp)) : IProp GF :=
  bigSepM (M := M) (fun _ pin => tx_pin capacity name pin.1 pin.2) pins

end MachCSL.Logic.LogTx
