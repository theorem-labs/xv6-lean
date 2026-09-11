import MachCSL.Logic.LockRankDefs
import MachCSL.Logic.EraDefs
import Iris.Algebra.LeibnizSet

/-! Source `LockSet.v`: disjoint name-set ownership. The singleton fragment
is exclusive, unlike the persistent dirty-set receipt. -/
namespace MachCSL.Logic.LockSet
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI Auth

abbrev Names := LockRank.Names
abbrev SetUR := DisjointLeibnizSet Names
abbrev SetRA := Auth SetUR
abbrev SetRF := constOF SetRA
def setFunctor : GFunctor := ⟨SetRF, inferInstance⟩

structure Capacity (GF : BundledGFunctors) where
  set : ElemG GF SetRF

def authElem (held : Names) : SetRA := ● (DisjointLeibnizSet.valid held)
def fragElem (name : String) : SetRA := ◯ (DisjointLeibnizSet.valid {name})

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def auth (γ : GName) (held : Names) : IProp GF :=
  iOwn (E := capacity.set) γ (authElem held)
def member (γ : GName) (name : String) : IProp GF :=
  iOwn (E := capacity.set) γ (fragElem name)
def level (γ : GName) (depth : Nat) (held : Names) : IProp GF :=
  iprop(auth capacity γ held ∗ ⌜held.size ≤ depth⌝)

/-- Canonical source era names, without an assertion that they were allocated. -/
def cpuLocks (era : Era.Record) (cpu : MachCSL.Machine.CPU) (held : Names) : IProp GF :=
  auth capacity (era.heldLocks cpu) held
def cpuMember (era : Era.Record) (cpu : MachCSL.Machine.CPU) (name : String) : IProp GF :=
  member capacity (era.heldLocks cpu) name
def cpuLevel (era : Era.Record) (cpu : MachCSL.Machine.CPU)
    (depth : Nat) (held : Names) : IProp GF :=
  level capacity (era.heldLocks cpu) depth held

end MachCSL.Logic.LockSet
