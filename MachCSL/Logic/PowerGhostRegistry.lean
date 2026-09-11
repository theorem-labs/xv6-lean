import MachCSL.Logic.PowerGhostDefs
import MachCSL.Logic.ReservationRegistry

/-! Reuse mono-nat slot3; add only observation-history ownership at slot11. -/
namespace MachCSL.Logic.PowerGhost
open Iris

abbrev ObservationRF := GhostVarF (List Machine.Observation)
def observationFunctor : GFunctor := ⟨ObservationRF, inferInstance⟩
def slot : Nat := 11
def registry : BundledGFunctors := Reservations.registry.set slot observationFunctor

theorem registry_other (i : Nat) (h : i ≠ slot) : registry i = Reservations.registry i := by
  simp [registry, BundledGFunctors.set, h]
theorem registry_old (i : Nat) (h : i < 11) : registry i = Reservations.registry i :=
  registry_other i (by unfold slot; omega)
theorem registry_unused (i : Nat) (h : 12 ≤ i) : registry i = Reservations.registry i :=
  registry_other i (by unfold slot; omega)

@[reducible] def observationSlot : ElemG registry ObservationRF := ⟨11, rfl⟩
def registryCapacity : Capacity registry := ⟨⟨3, rfl⟩, { elemG := observationSlot }⟩
def reservationCapacity : Reservations.Capacity registry := ⟨⟨⟨10, rfl⟩⟩⟩
def deviceCapacity : Device.Capacity registry :=
  ⟨{ elemG := ⟨7, rfl⟩ }, { elemG := ⟨8, rfl⟩ }, { elemG := ⟨9, rfl⟩ }⟩
def registerCapacity : Registers.Capacity registry := ⟨⟨⟨6, rfl⟩⟩⟩
def historyCapacity : Tso.History.Capacity registry := ⟨⟨⟨4, rfl⟩⟩, ⟨5, rfl⟩⟩
def viewsCapacity : Tso.Views.Capacity registry := ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩
def ledgerCapacity : Tso.Capacity registry := ⟨⟨⟨0, rfl⟩⟩, ⟨⟨1, rfl⟩⟩⟩

theorem sharedNat_same : registryCapacity.sharedNat = viewsCapacity.sharedNat := rfl

theorem genAuth_eq_shared_views (γ : GName) (n : Nat) :
    genAuth registryCapacity γ n = Tso.Views.natAuth viewsCapacity γ (.own 1) n := rfl

end MachCSL.Logic.PowerGhost
