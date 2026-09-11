import MachCSL.Logic.DiskDefs
import MachCSL.Logic.PowerGhostRegistry

namespace MachCSL.Logic.Disk
open Iris

def slot : Nat := 12
def registry : BundledGFunctors := PowerGhost.registry.set slot imageFunctor

theorem registry_other (i : Nat) (h : i ≠ slot) : registry i = PowerGhost.registry i := by
  simp [registry, BundledGFunctors.set, h]
theorem registry_old (i : Nat) (h : i < 12) : registry i = PowerGhost.registry i :=
  registry_other i (by unfold slot; omega)
theorem registry_unused (i : Nat) (h : 13 ≤ i) : registry i = PowerGhost.registry i :=
  registry_other i (by unfold slot; omega)

@[reducible] def imageSlot : ElemG registry ImageRF := ⟨12, rfl⟩
def registryCapacity : Capacity registry := ⟨⟨imageSlot⟩⟩
def powerCapacity : PowerGhost.Capacity registry := ⟨⟨3, rfl⟩, { elemG := ⟨11, rfl⟩ }⟩
def reservationCapacity : Reservations.Capacity registry := ⟨⟨⟨10, rfl⟩⟩⟩
def deviceCapacity : Device.Capacity registry :=
  ⟨{ elemG := ⟨7, rfl⟩ }, { elemG := ⟨8, rfl⟩ }, { elemG := ⟨9, rfl⟩ }⟩
def registerCapacity : Registers.Capacity registry := ⟨⟨⟨6, rfl⟩⟩⟩
def historyCapacity : Tso.History.Capacity registry := ⟨⟨⟨4, rfl⟩⟩, ⟨5, rfl⟩⟩
def viewsCapacity : Tso.Views.Capacity registry := ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩
def ledgerCapacity : Tso.Capacity registry := ⟨⟨⟨0, rfl⟩⟩, ⟨⟨1, rfl⟩⟩⟩

end MachCSL.Logic.Disk
