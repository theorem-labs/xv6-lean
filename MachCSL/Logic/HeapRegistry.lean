import MachCSL.Logic.HeapDefs
import MachCSL.Logic.DiskRegistry

/-! Add only the two native gen_heap metadata cameras; byte ownership stays at slot zero. -/
namespace MachCSL.Logic.Heap
open Iris

def metadataMapFunctor : GFunctor := ⟨MetadataMapRF, inferInstance⟩
def metadataFunctor : GFunctor := ⟨MetadataRF, inferInstance⟩

inductive Slot where
  | metadataMap
  | metadata
  deriving DecidableEq

def Slot.index : Slot → Nat
  | .metadataMap => 13
  | .metadata => 14

theorem Slot.index_injective {a b : Slot} (h : a.index = b.index) : a = b := by
  cases a <;> cases b <;> simp_all [index]

def registry : BundledGFunctors :=
  (Disk.registry.set Slot.metadataMap.index metadataMapFunctor).set Slot.metadata.index metadataFunctor

theorem registry_old (i : Nat) (h : i < 13) : registry i = Disk.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 13 by omega, show i ≠ 14 by omega]

theorem registry_unused (i : Nat) (h : 15 ≤ i) : registry i = Disk.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 13 by omega, show i ≠ 14 by omega]

@[reducible] def metadataMapSlot : ElemG registry MetadataMapRF := ⟨13, rfl⟩
@[reducible] def metadataSlot : ElemG registry MetadataRF := ⟨14, rfl⟩

def ledgerCapacity : Tso.Capacity registry := ⟨⟨⟨0, rfl⟩⟩, ⟨⟨1, rfl⟩⟩⟩
def registryCapacity : Capacity registry := ⟨ledgerCapacity, ⟨metadataMapSlot⟩, metadataSlot⟩
def diskCapacity : Disk.Capacity registry := ⟨⟨⟨12, rfl⟩⟩⟩
def powerCapacity : PowerGhost.Capacity registry := ⟨⟨3, rfl⟩, { elemG := ⟨11, rfl⟩ }⟩
def reservationCapacity : Reservations.Capacity registry := ⟨⟨⟨10, rfl⟩⟩⟩
def deviceCapacity : Device.Capacity registry :=
  ⟨{ elemG := ⟨7, rfl⟩ }, { elemG := ⟨8, rfl⟩ }, { elemG := ⟨9, rfl⟩ }⟩
def registerCapacity : Registers.Capacity registry := ⟨⟨⟨6, rfl⟩⟩⟩
def historyCapacity : Tso.History.Capacity registry := ⟨⟨⟨4, rfl⟩⟩, ⟨5, rfl⟩⟩
def viewsCapacity : Tso.Views.Capacity registry := ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩

theorem ledger_same : registryCapacity.ledger = ledgerCapacity := rfl
theorem byte_slot_zero : registryCapacity.preS.heap.elem.τ = 0 := rfl

end MachCSL.Logic.Heap
