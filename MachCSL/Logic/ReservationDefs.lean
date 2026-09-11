import MachCSL.Machine.State
import Iris.Instances.Lib.GhostMap
import Iris.Std.HeapInstances
import Init.Data.List.FinRange

/-! Full finite reservation mirror from `RiscvPtsto.v:1984–2071`, paper pin.
The values are actual optional reservation snapshots, not booleans or addresses.
-/
namespace MachCSL.Logic.Reservations
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI MachCSL.Machine

abbrev Value := Option Reservation
abbrev ReservationMap (V : Type) := _root_.Std.ExtTreeMap CPU V
abbrev ReservationRA := HeapView CPU (Agree (DiscreteO Value)) ReservationMap
abbrev ReservationRF := constOF ReservationRA

def reservationFunctor : GFunctor := ⟨ReservationRF, inferInstance⟩

/-- Uninitialized capacity only. An era's runtime name is always a separate argument. -/
structure Capacity (GF : BundledGFunctors) where
  reservations : GhostMapG GF CPU Value ReservationMap

/-- Insert all enumerated CPUs; duplicate enumeration would retain the same value. -/
def mapCpus (f : CPU → Value) : List CPU → ReservationMap Value
  | [] => ∅
  | cpu :: rest => PartialMap.insert (mapCpus f rest) cpu (f cpu)

/-- Contains every CPU key. An unreserved CPU is mapped to `some none`, not absent. -/
def resvMap (f : CPU → Value) : ReservationMap Value := mapCpus f (List.finRange 8)

def noneMap : ReservationMap Value := resvMap (fun _ => none)

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def resvAuth (γ : GName) (f : CPU → Value) : IProp GF :=
  letI := capacity.reservations
  ghost_map_auth γ (.own 1) (resvMap f)

def resvFrag (γ : GName) (cpu : CPU) (value : Value) : IProp GF :=
  letI := capacity.reservations
  ghost_map_elem γ (.own 1) cpu value

def resvAny (γ : GName) (cpu : CPU) : IProp GF :=
  iprop(∃ value : Value, resvFrag capacity γ cpu value)

/-- All eight per-hart fragments exported by native allocation. -/
def allFragments (γ : GName) (f : CPU → Value) : IProp GF :=
  letI := capacity.reservations
  iprop([∗map] cpu ↦ value ∈ resvMap f, ghost_map_elem γ (.own 1) cpu value)

end MachCSL.Logic.Reservations
