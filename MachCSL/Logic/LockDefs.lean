import MachCSL.Machine.Platform
import Iris.Algebra.Lib.ExclAuth
import Iris.Instances.IProp

/-! Exact spinlock camera from `Xv6Cameras.v:101–112` and the native
ownership predicates from `WpLock.v:88–98`. The acquisition position is a
separate authoritative component, not an omitted or guessed timestamp. -/
namespace MachCSL.Logic.Lock
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

abbrev State := Option (MachCSL.Machine.CPU × Bool)
abbrev StateRA := ExclAuth.ExclAuthUR (A := DiscreteO State)
abbrev PositionRA := ExclAuth.ExclAuthUR (A := DiscreteO Nat)
abbrev LockRA := StateRA × PositionRA
abbrev LockRF := constOF LockRA
def lockFunctor : GFunctor := ⟨LockRF, inferInstance⟩

structure Capacity (GF : BundledGFunctors) where
  lock : ElemG GF LockRF

def authElem (state : State) (position : Nat) : LockRA :=
  (ExclAuth.auth ⟨state⟩, ExclAuth.auth ⟨position⟩)
def fragElem (state : State) (position : Nat) : LockRA :=
  (ExclAuth.frag ⟨state⟩, ExclAuth.frag ⟨position⟩)

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def authAt (γ : GName) (state : State) (position : Nat) : IProp GF :=
  iOwn (E := capacity.lock) γ (authElem state position)
def fragAt (γ : GName) (state : State) (position : Nat) : IProp GF :=
  iOwn (E := capacity.lock) γ (fragElem state position)
def auth (γ : GName) (state : State) : IProp GF := iprop(∃ position : Nat, authAt capacity γ state position)
def frag (γ : GName) (state : State) : IProp GF := iprop(∃ position : Nat, fragAt capacity γ state position)

end MachCSL.Logic.Lock
