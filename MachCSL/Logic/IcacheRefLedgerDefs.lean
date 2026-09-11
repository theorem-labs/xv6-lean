import Iris.Algebra.Heap
import Iris.Algebra.Auth
import Iris.Algebra.Excl
import Iris.Algebra.Numbers
import Iris.Algebra.LocalUpdates
import Iris.Std.HeapInstances
import Iris.Std.GenSetsInstances
import Iris.Instances.IProp

/-! Source inode-reference ledger: per-inum authoritative nested columns,
separate from the filesystem's typed directory-link multiset camera. -/
namespace MachCSL.Logic.IcacheRefLedger
open Iris Iris.Std Iris.CMRA Iris.BI
open scoped CommMonoidLike

/-- Additive naturals with zero core; a newtype keeps this camera distinct
from the source monotone-max counters already used elsewhere. -/
@[ext] structure NatAdd where
  value : Nat
  deriving DecidableEq
instance : Add NatAdd := ⟨fun a b => ⟨a.value + b.value⟩⟩
instance : Zero NatAdd := ⟨⟨0⟩⟩
instance (n : Nat) : OfNat NatAdd n := ⟨⟨n⟩⟩
instance : LE NatAdd := ⟨fun a b => a.value ≤ b.value⟩
instance : _root_.Std.Associative (α := NatAdd) (· + ·) := ⟨fun a b c => by cases a; cases b; cases c; exact NatAdd.ext (Nat.add_assoc _ _ _)⟩
instance : _root_.Std.Commutative (α := NatAdd) (· + ·) := ⟨fun a b => NatAdd.ext (Nat.add_comm a.value b.value)⟩
instance : _root_.Std.LawfulLeftIdentity (α := NatAdd) (· + ·) 0 where
  left_id a := NatAdd.ext (Nat.zero_add a.value)
instance : LeftCancelAdd NatAdd := ⟨fun h => NatAdd.ext (Nat.add_left_cancel (congrArg NatAdd.value h))⟩
instance : LawfulAddLE NatAdd where
  le_iff_exists_add := by
    intro x y
    constructor
    · intro h
      change x.value ≤ y.value at h
      exact ⟨⟨y.value - x.value⟩, NatAdd.ext (by change y.value = x.value + (y.value - x.value); omega)⟩
    · rintro ⟨z, rfl⟩
      change x.value ≤ x.value + z.value
      omega
instance : COFE NatAdd := COFE.ofDiscrete _
instance : OFE.Discrete NatAdd := ⟨fun h => h⟩
instance : CMRA NatAdd := CommMonoidLike.instCMRA
instance : UCMRA NatAdd := CommMonoidLike.instUCMRA
instance : CMRA.Discrete NatAdd := CommMonoidLike.instDiscrete

abbrev ClaimValue := BitVec 16 × (Nat × Qp)
abbrev FreezeIndex := Bool × (Nat × Qp)
inductive Freeze where
  | off
  | pre (index : FreezeIndex)
  | post (index : FreezeIndex)
  deriving DecidableEq
abbrev ClaimCell := Option (Excl (DiscreteO ClaimValue))
abbrev FreezeCell := Option (Excl (DiscreteO Freeze))
abbrev Element0 := ClaimCell × NatAdd
abbrev Element1 := Element0 × FreezeCell
abbrev Element := Element1 × NatAdd
abbrev LedgerMap (V : Type) := _root_.Std.ExtTreeMap Int V
abbrev LedgerRA := LedgerMap (Auth Element)
instance : CMRA LedgerRA := Heap.instStoreCMRA (M := LedgerMap) (K := Int)
instance : UCMRA LedgerRA := Heap.instStoreUCMRA (M := LedgerMap) (K := Int)
abbrev LedgerRF := constOF LedgerRA
def ledgerFunctor : GFunctor := ⟨LedgerRF, inferInstance⟩
structure Capacity (GF : BundledGFunctors) where
  ledger : ElemG GF LedgerRF

def claimCell (ty : BitVec 16) (t : Nat) (q : Qp) : ClaimCell := some (.excl ⟨(ty, t, q)⟩)
def freezeCell (phase : Freeze) : FreezeCell := some (.excl ⟨phase⟩)
def lelem0 (c : ClaimCell) (r : Nat) : Element0 := (c, ⟨r⟩)
def lelemc (c : ClaimCell) (r : Nat) (f : FreezeCell) (rc : Nat) : Element := ((lelem0 c r, f), ⟨rc⟩)
def lelemf (c : ClaimCell) (r : Nat) (f : FreezeCell) : Element := lelemc c r f 0
def lelem (c : ClaimCell) (r : Nat) : Element := lelemf c r none

def frz_ispre : Freeze → Bool | .pre _ => true | _ => false
def frz_preb : FreezeCell → Bool | some (.excl phase) => frz_ispre phase.car | _ => false
def frz_reg : Freeze → Option FreezeIndex | .off => none | .pre index | .post index => some index

def authElem (i : Int) (a : Element) : LedgerRA := PartialMap.singleton (M := LedgerMap) i (● a)
def fragElem (i : Int) (a : Element) : LedgerRA := PartialMap.singleton (M := LedgerMap) i (◯ a)
def lelem_boot : Element := lelemf none 0 (freezeCell .off)
def bootMap (inums : _root_.Std.ExtTreeSet Int) : LedgerRA :=
  FiniteMap.ofSet (M := LedgerMap) ((● lelem_boot : Auth Element) • ◯ lelem_boot) inums

variable {GF : BundledGFunctors} (capacity : Capacity GF) (g : GName)
def link_auth_e (i : Int) (a : Element) : IProp GF := iOwn (E := capacity.ledger) g (authElem i a)
def link_frag_e (i : Int) (a : Element) : IProp GF := iOwn (E := capacity.ledger) g (fragElem i a)
def link_auth (i : Int) (c : ClaimCell) (r : Nat) (f : FreezeCell) (rc : Nat) : IProp GF :=
  link_auth_e capacity g i (lelemc c r f rc)
def iclaim (i : Int) (ty : BitVec 16) (t : Nat) (q : Qp) : IProp GF :=
  link_frag_e capacity g i (lelem (claimCell ty t q) 0)
def runit_plain (i : Int) : IProp GF := link_frag_e capacity g i (lelem none 1)
def runit_claim (i : Int) : IProp GF := link_frag_e capacity g i (lelemc none 0 none 1)
def runit (flavor : Bool) (i : Int) : IProp GF := if flavor then runit_claim capacity g i else runit_plain capacity g i
/-- Source C' conversion discipline: a resting reference is plain. -/
def runit_any (i : Int) : IProp GF := runit_plain capacity g i

def rup (flavor : Bool) (r : Nat) : Nat := if flavor then r else r + 1
def rcup (flavor : Bool) (rc : Nat) : Nat := if flavor then rc + 1 else rc

def ifreeze (phase : Freeze) (i : Int) : IProp GF := link_frag_e capacity g i (lelemf none 0 (freezeCell phase))
def ifreeze_off (i : Int) : IProp GF := ifreeze capacity g .off i
def ifreeze_pre (index : FreezeIndex) (i : Int) : IProp GF := ifreeze capacity g (.pre index) i
def ifreeze_post (index : FreezeIndex) (i : Int) : IProp GF := ifreeze capacity g (.post index) i

def bootOwned (inums : _root_.Std.ExtTreeSet Int) : IProp GF := iOwn (E := capacity.ledger) g (bootMap inums)
def bootRows (inums : _root_.Std.ExtTreeSet Int) : IProp GF :=
  bigSepS (fun i => iprop(link_auth capacity g i none 0 (freezeCell .off) 0 ∗ ifreeze_off capacity g i)) inums

end MachCSL.Logic.IcacheRefLedger
