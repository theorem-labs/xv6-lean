import Iris.Algebra.Csum
import Iris.Algebra.Excl
import Iris.Algebra.Agree
import Iris.Instances.IProp

/-! The exact non-unital type one-shot from `Xv6Cameras.v:613` and
`IcacheRef.v:1192–1298`. Its separate boot name uses the same camera. -/
namespace MachCSL.Logic.IcacheTypeGhost
open Iris Iris.BI

abbrev TypeRA := Csum (Excl Unit) (Agree (DiscreteO (BitVec 16)))
abbrev TypeRF := constOF TypeRA
def typeFunctor : GFunctor := ⟨TypeRF, inferInstance⟩
structure Capacity (GF : BundledGFunctors) where
  type : ElemG GF TypeRF

def pendingElem : TypeRA := .inl (.excl ())
def shotElem (ty : BitVec 16) : TypeRA := .inr (toAgree ⟨ty⟩)

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def ity_pending (g : GName) : IProp GF := iOwn (E := capacity.type) g pendingElem
def ity_shot (g : GName) (ty : BitVec 16) : IProp GF := iOwn (E := capacity.type) g (shotElem ty)
def ireg_boot (bootName : GName) : IProp GF := ity_pending capacity bootName
def ireg_open (bootName : GName) : IProp GF := iprop(∃ ty : BitVec 16, ity_shot capacity bootName ty)
def ireg_regime (bootName : GName) (runtime : Bool) : IProp GF :=
  if runtime then ireg_open capacity bootName else ireg_boot capacity bootName

end MachCSL.Logic.IcacheTypeGhost
