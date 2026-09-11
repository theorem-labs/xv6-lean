import MachCSL.Logic.TsoViewsDefs
import Iris.Algebra.LeibnizSet
import Iris.Std.GenSetsInstances

namespace MachCSL.Logic.LogEpoch
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI
attribute [local instance] lexOrd
abbrev LoggedSet := _root_.Std.ExtTreeSet (Nat × Int)
abbrev LoggedUR := LeibnizSet LoggedSet
abbrev LoggedRF := constOF (Auth LoggedUR)
def loggedFunctor : GFunctor := ⟨LoggedRF, inferInstance⟩

structure Capacity (GF : BundledGFunctors) where
  epoch : ElemG GF MonoNatRF
  logged : ElemG GF LoggedRF

@[reducible] def Capacity.monoNat {GF : BundledGFunctors} (capacity : Capacity GF)
    (name : GName) : MonoNatG GF := ⟨capacity.epoch, name⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)
def epochAuth (name : GName) (epoch : Nat) : IProp GF :=
  letI := capacity.monoNat name
  MonoNat.auth_own name (.own 1) (.ofNat epoch)
def log_epoch_lb (name : GName) (epoch : Nat) : IProp GF :=
  letI := capacity.monoNat name
  MonoNat.lb_own name (.ofNat epoch)
def loggedAuth (name : GName) (entries : LoggedSet) : IProp GF :=
  iOwn (E := capacity.logged) name (● (LeibnizSet.valid entries : LoggedUR))
def logged_at (name : GName) (epoch : Nat) (block : Int) : IProp GF :=
  iOwn (E := capacity.logged) name (◯ (LeibnizSet.valid {(epoch, block)} : LoggedUR))

end MachCSL.Logic.LogEpoch
