import Iris.Algebra.Heap
import Iris.Algebra.Lib.DFracAgree
import Iris.Std.HeapInstances
import Iris.Std.GenSetsInstances
import Iris.Instances.IProp

/-! Three distinct source icache coupling cameras. These are pointwise
fraction/agreement maps, with no authoritative column or per-key ghost names. -/
namespace MachCSL.Logic.IcacheCoupling
open Iris Iris.Std Iris.CMRA Iris.BI

abbrev Cell (A : Type) := DFracAgree.DFracAgreeR (DiscreteO A)
abbrev InumMap (V : Type) := _root_.Std.ExtTreeMap Int V
abbrev SlotMap (V : Type) := _root_.Std.ExtTreeMap Nat V
abbrev Inums := _root_.Std.ExtTreeSet Int
abbrev PinValue := Option (Nat × Qp)
abbrev CountRA := InumMap (Cell Nat)
abbrev MirrorRA := InumMap (Cell Bool)
abbrev PinRA := SlotMap (Cell PinValue)
instance : CMRA CountRA := Heap.instStoreCMRA (M := InumMap) (K := Int)
instance : UCMRA CountRA := Heap.instStoreUCMRA (M := InumMap) (K := Int)
instance : CMRA MirrorRA := Heap.instStoreCMRA (M := InumMap) (K := Int)
instance : UCMRA MirrorRA := Heap.instStoreUCMRA (M := InumMap) (K := Int)
instance : CMRA PinRA := Heap.instStoreCMRA (M := SlotMap) (K := Nat)
instance : UCMRA PinRA := Heap.instStoreUCMRA (M := SlotMap) (K := Nat)
abbrev CountRF := constOF CountRA
abbrev MirrorRF := constOF MirrorRA
abbrev PinRF := constOF PinRA
def countFunctor : GFunctor := ⟨CountRF, inferInstance⟩
def mirrorFunctor : GFunctor := ⟨MirrorRF, inferInstance⟩
def pinFunctor : GFunctor := ⟨PinRF, inferInstance⟩

structure Capacity (GF : BundledGFunctors) where
  count : ElemG GF CountRF
  mirror : ElemG GF MirrorRF
  pin : ElemG GF PinRF
structure Names where
  count : GName
  mirror : GName
  pin : GName

def countElem (i : Int) (q : Qp) (n : Nat) : CountRA :=
  PartialMap.singleton (M := InumMap) i (DFracAgree.Frac.mk q ⟨n⟩)
def mirrorElem (i : Int) (q : Qp) (b : Bool) : MirrorRA :=
  PartialMap.singleton (M := InumMap) i (DFracAgree.Frac.mk q ⟨b⟩)
def pinElem (k : Nat) (q : Qp) (v : PinValue) : PinRA :=
  PartialMap.singleton (M := SlotMap) k (DFracAgree.Frac.mk q ⟨v⟩)

def countBootMap (inums : Inums) : CountRA :=
  FiniteMap.ofSet (M := InumMap) (DFracAgree.Frac.mk 1 (⟨0⟩ : DiscreteO Nat)) inums
def mirrorBootMap (inums : Inums) : MirrorRA :=
  FiniteMap.ofSet (M := InumMap) (DFracAgree.Frac.mk 1 (⟨false⟩ : DiscreteO Bool)) inums
/-- Source NINODE is 50; this map follows its ordered list big operation. -/
def pinBootMap : PinRA := (List.range 50).foldr (fun k rest => pinElem k 1 none • rest) UCMRA.unit

variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)
def icnt_at (i : Int) (q : Qp) (n : Nat) : IProp GF := iOwn (E := capacity.count) names.count (countElem i q n)
def icnt_half (i : Int) (n : Nat) : IProp GF := icnt_at capacity names i (1 : Qp).half n
def icnt_full (i : Int) (n : Nat) : IProp GF := icnt_at capacity names i 1 n
def frzm_at (i : Int) (q : Qp) (b : Bool) : IProp GF := iOwn (E := capacity.mirror) names.mirror (mirrorElem i q b)
def frzm_h (i : Int) (b : Bool) : IProp GF := frzm_at capacity names i (1 : Qp).half b
def frzm_full (i : Int) (b : Bool) : IProp GF := frzm_at capacity names i 1 b
def hpn_at (k : Nat) (q : Qp) (v : PinValue) : IProp GF := iOwn (E := capacity.pin) names.pin (pinElem k q v)
def hpn_h (k : Nat) (v : PinValue) : IProp GF := hpn_at capacity names k (1 : Qp).half v
def hpn_full (k : Nat) (v : PinValue) : IProp GF := hpn_at capacity names k 1 v

def countMapOwned (inums : Inums) : IProp GF := iOwn (E := capacity.count) names.count (countBootMap inums)
def mirrorMapOwned (inums : Inums) : IProp GF := iOwn (E := capacity.mirror) names.mirror (mirrorBootMap inums)
def pinMapOwned : IProp GF := iOwn (E := capacity.pin) names.pin pinBootMap

def bootCounts (inums : Inums) : IProp GF :=
  bigSepS (fun i => iprop(icnt_half capacity names i 0 ∗ icnt_half capacity names i 0)) inums
def bootMirrors (inums : Inums) : IProp GF :=
  bigSepS (fun i => iprop(frzm_h capacity names i false ∗ frzm_h capacity names i false)) inums
def bootPins : IProp GF := bigSepL (fun _ k => hpn_full capacity names k none) (List.range 50)

end MachCSL.Logic.IcacheCoupling
