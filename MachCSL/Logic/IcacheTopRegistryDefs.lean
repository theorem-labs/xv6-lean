import MachCSL.Logic.FsTopDefs
import MachCSL.Logic.LogTxDefs
import Iris.Instances.Lib.Invariants

namespace MachCSL.Logic.IcacheTopRegistry
open Iris Iris.Std Iris.Algebra Iris.BI

abbrev InumSet := _root_.Std.ExtTreeSet Int
abbrev Entry := (Nat × Qp) × InumSet
abbrev ArmMap (V : Type) := _root_.Std.ExtTreeMap Nat V
abbrev ArmRA := HeapView Nat (Agree (DiscreteO Entry)) ArmMap
abbrev ArmRF := constOF ArmRA
def armFunctor : GFunctor := ⟨ArmRF, inferInstance⟩
structure Capacity (GF : BundledGFunctors) where
  arms : GhostMapG GF Nat Entry ArmMap
  top : FsTop.Capacity GF
  transactions : LogTx.Capacity GF
structure Names where
  top : GName
  arms : GName
  transactions : GName

def clean (nodes : Xv6.Fs.DurableState.InodeMap) (arms : ArmMap Entry) : Prop :=
  ∀ i node, nodes[i]? = some node →
    (∀ (k t : Nat) (q : Qp) (S : InumSet), get? arms k = some ((t, q), S) → i ∉ S) → Xv6.Fs.DurableNode.Local i node

variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)

def armAuth (arms : ArmMap Entry) : IProp GF :=
  letI := capacity.arms
  ghost_map_auth names.arms (.own 1) arms
def parked (entry : Entry) : IProp GF :=
  LogTx.tx_pin capacity.transactions names.transactions entry.1.1 entry.1.2
def armed (k t : Nat) (q : Qp) (S : InumSet) : IProp GF :=
  letI := capacity.arms
  ghost_map_elem names.arms (.own 1) k ((t, q), S)
def parkedMap (arms : ArmMap Entry) : IProp GF :=
  bigSepM (M := ArmMap) (fun _ entry => parked capacity names entry) arms
def body : IProp GF :=
  iprop(∃ (nodes : Xv6.Fs.DurableState.InodeMap) (arms : ArmMap Entry),
    FsTop.auth capacity.top names.top nodes ∗ armAuth capacity names arms ∗
    parkedMap capacity names arms ∗ ⌜clean nodes arms⌝)
def invariant {hlc : HasLC} [InvGS_gen hlc GF] (N : Namespace) : IProp GF :=
  inv N (body capacity names)

end MachCSL.Logic.IcacheTopRegistry
