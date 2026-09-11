import MachCSL.Logic.ReservationDefs
import MachCSL.Logic.DeviceRegistry

namespace MachCSL.Logic.Reservations
open Iris

/-- Reservation mirror follows register6 and device7–9, sharing the old mono-nat. -/
def slot : Nat := 10
def registry : BundledGFunctors := Device.registry.set slot reservationFunctor

theorem registry_other (i : Nat) (h : i ≠ slot) : registry i = Device.registry i := by
  simp [registry, BundledGFunctors.set, h]

theorem registry_old (i : Nat) (h : i < 10) : registry i = Device.registry i :=
  registry_other i (by unfold slot; omega)

theorem registry_unused (i : Nat) (h : 11 ≤ i) : registry i = Device.registry i :=
  registry_other i (by unfold slot; omega)

@[reducible] def reservationSlot : ElemG registry ReservationRF := ⟨10, rfl⟩
def registryCapacity : Capacity registry := ⟨⟨reservationSlot⟩⟩
def deviceCapacity : Device.Capacity registry :=
  ⟨{ elemG := ⟨7, rfl⟩ }, { elemG := ⟨8, rfl⟩ }, { elemG := ⟨9, rfl⟩ }⟩
def registerCapacity : Registers.Capacity registry := ⟨⟨⟨6, rfl⟩⟩⟩
def historyCapacity : Tso.History.Capacity registry := ⟨⟨⟨4, rfl⟩⟩, ⟨5, rfl⟩⟩
def viewsCapacity : Tso.Views.Capacity registry := ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩
def ledgerCapacity : Tso.Capacity registry := ⟨⟨⟨0, rfl⟩⟩, ⟨⟨1, rfl⟩⟩⟩

end MachCSL.Logic.Reservations
