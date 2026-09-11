import MachCSL.Logic.TsoGhost
import Iris.Algebra.Functions
import Iris.Algebra.LocalUpdates
import Iris.BI.Lib.MonoNat

/-! The source `TsoGhost.viewUR` and its explicit resource capacity.
The carrier is the total function on every Nat agent, not only the CPU set.
The demonstration extension leaves the existing byte/timestamp registry intact
and installs one shared mono-nat slot, reusable by log lengths and generations. -/
namespace MachCSL.Logic.Tso.Views
open MachCSL.Memory Iris Iris.Algebra Iris.CMRA Iris.BI Auth

abbrev ViewUR := Agent → MaxNat

def vf (views : Agent → Nat) : ViewUR := fun h => .ofNat (views h)
def vone (h : Agent) (bound : Nat) : ViewUR := fun other =>
  .ofNat (if other = h then bound else 0)

instance vf_coreId (views : Agent → Nat) : CoreId (vf views) := ⟨rfl⟩
instance vone_coreId (h : Agent) (bound : Nat) : CoreId (vone h bound) := ⟨rfl⟩

theorem vf_valid (views : Agent → Nat) : ✓ vf views := fun _ => trivial

theorem vone_incl_vf (h : Agent) (bound : Nat) (views : Agent → Nat)
    (le : bound ≤ views h) : vone h bound ≼ vf views := by
  refine ⟨vf views, ?_⟩
  funext other
  apply (MaxNat.eq_toNat _ _).mpr
  change views other = max (if other = h then bound else 0) (views other)
  by_cases he : other = h
  · subst other
    simp [le]
  · simp [he]

theorem vone_le_incl (h : Agent) (bound lower : Nat) (le : lower ≤ bound) :
    vone h lower ≼ vone h bound := by
  refine ⟨vone h bound, ?_⟩
  funext other
  apply (MaxNat.eq_toNat _ _).mpr
  change (if other = h then bound else 0) =
    max (if other = h then lower else 0) (if other = h then bound else 0)
  by_cases he : other = h <;> simp [he, le]

theorem vf_local_update (views views' : Agent → Nat) (le : ∀ h, views h ≤ views' h) :
    (vf views, vf views) ~l~> (vf views', vf views') :=
  LocalUpdate.discrete_fun (fun h => MaxNat.local_update (le h))

abbrev ViewRF := constOF (Auth ViewUR)

def viewFunctor : GFunctor := ⟨ViewRF, inferInstance⟩
def sharedNatFunctor : GFunctor := ⟨MonoNatRF, inferInstance⟩

/-- Capacity only: no runtime ghost name or initialized resource is stored here. -/
structure Capacity (GF : BundledGFunctors) where
  views : ElemG GF ViewRF
  sharedNat : ElemG GF MonoNatRF

inductive Slot where
  | views
  | sharedNat
  deriving DecidableEq

def Slot.index : Slot → Nat
  | .views => 2
  | .sharedNat => 3

theorem Slot.index_injective {a b : Slot} (h : a.index = b.index) : a = b := by
  cases a <;> cases b <;> simp_all [index]

/-- A separate four-slot extension; the previous registry is not redefined. -/
def registry : BundledGFunctors :=
  (Tso.registry.set Slot.views.index viewFunctor).set Slot.sharedNat.index sharedNatFunctor

theorem registry_old (i : Nat) (h : i < 2) : registry i = Tso.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 2 by omega, show i ≠ 3 by omega]

theorem registry_unused (i : Nat) (h : 4 ≤ i) : registry i = Tso.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 2 by omega, show i ≠ 3 by omega]

@[reducible] def viewSlot : ElemG registry ViewRF := ⟨2, rfl⟩
@[reducible] def sharedNatSlot : ElemG registry MonoNatRF := ⟨3, rfl⟩

def registryCapacity : Capacity registry := ⟨viewSlot, sharedNatSlot⟩

/-- The previous two capacities are also derived, rather than assumed, in this extension. -/
def ledgerCapacity : Tso.Capacity registry := ⟨⟨⟨0, rfl⟩⟩, ⟨⟨1, rfl⟩⟩⟩

/-- Native MonoNatG has an extra name field. Adapt it using the explicitly
supplied runtime name; all native auth/lb assertions also take that name. -/
@[reducible] def Capacity.monoNat {GF : BundledGFunctors} (c : Capacity GF)
    (name : GName) : MonoNatG GF := ⟨c.sharedNat, name⟩

variable {GF : BundledGFunctors} (capacity : Capacity GF)

abbrev natAuth (name : GName) (dq : DFrac) (n : Nat) : IProp GF :=
  letI := capacity.monoNat name
  MonoNat.auth_own name dq (.ofNat n)

abbrev natLB (name : GName) (n : Nat) : IProp GF :=
  letI := capacity.monoNat name
  MonoNat.lb_own name (.ofNat n)

/-- Source `llb`, including its pure zero-bound branch. -/
def llb (name : GName) (bound : Nat) : IProp GF :=
  iprop(natLB capacity name bound ∨ ⌜bound = 0⌝)

/-- Source `view_auth`: the authority and fragment have the same whole view function. -/
def viewAuth (name : GName) (views : Agent → Nat) : IProp GF :=
  iOwn (E := capacity.views) name ((● vf views) • ◯ vf views)

def viewFrag (name : GName) (h : Agent) (bound : Nat) : IProp GF :=
  iOwn (E := capacity.views) name (◯ vone h bound)

/-- Source `view_lb`: a view fragment and log-length receipt, or the pure zero fact. -/
def viewLB (viewName logName : GName) (h : Agent) (bound : Nat) : IProp GF :=
  iprop((viewFrag capacity viewName h bound ∗ natLB capacity logName bound) ∨ ⌜bound = 0⌝)

end MachCSL.Logic.Tso.Views
