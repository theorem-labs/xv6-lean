import Iris.Algebra.Heap
import Iris.Algebra.LeibnizMultiSet
import Iris.Algebra.Auth
import Iris.Std.GenMultiSetsInstances
import Iris.Std.HeapInstances
import Iris.Instances.IProp

/-! Exact FsStateLink type-register camera: a finite per-inode map of
an authoritative finite multiset of file/directory-parent values. -/
namespace MachCSL.Logic.FsLink
open Iris Iris.Std Iris.CMRA Iris.BI

inductive IType where
  | file
  | directory (parent : Int)
  deriving DecidableEq, Repr

abbrev Pile := ListPerm IType
abbrev PileRA := LeibnizMultiSet Pile
abbrev ElementRA := Auth PileRA
abbrev FamilyMap (V : Type) := _root_.Std.ExtTreeMap Int V
abbrev FamilyRA := FamilyMap ElementRA

instance : CMRA FamilyRA := Heap.instStoreCMRA (M := FamilyMap) (K := Int)
instance : UCMRA FamilyRA := Heap.instStoreUCMRA (M := FamilyMap) (K := Int)
abbrev LinkRF := constOF FamilyRA

structure Capacity (GF : BundledGFunctors) where
  link : ElemG GF LinkRF

def reps (n : Nat) (ty : IType) : Pile := ListPerm.ofList (List.replicate n ty)

def authElem (inum : Int) (n : Nat) (ty : IType) : FamilyRA :=
  PartialMap.singleton (M := FamilyMap) inum (● (LeibnizMultiSet.ofSet (reps n ty)))
def toksElem (inum : Int) (pile : Pile) : FamilyRA :=
  PartialMap.singleton (M := FamilyMap) inum (◯ (LeibnizMultiSet.ofSet pile))
def tokElem (inum : Int) (ty : IType) : FamilyRA := toksElem inum {ty}
def fullElem (inum : Int) (n : Nat) (ty : IType) : FamilyRA :=
  authElem inum n ty • toksElem inum (reps n ty)

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def auth (γ : GName) (inum : Int) (n : Nat) (ty : IType) : IProp GF :=
  iOwn (E := capacity.link) γ (authElem inum n ty)
def toks (γ : GName) (inum : Int) (pile : Pile) : IProp GF :=
  iOwn (E := capacity.link) γ (toksElem inum pile)
def tok (γ : GName) (inum : Int) (ty : IType) : IProp GF := toks capacity γ inum {ty}

end MachCSL.Logic.FsLink
