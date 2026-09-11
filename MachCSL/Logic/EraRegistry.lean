import MachCSL.Logic.EraDefs
import MachCSL.Logic.HeapRegistry

namespace MachCSL.Logic.Era
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

abbrev RegistryMap (V : Type) := _root_.Std.ExtTreeMap Nat V
abbrev RegistryRA := HeapView Nat (Agree (DiscreteO Record)) RegistryMap
abbrev RegistryRF := constOF RegistryRA
def registryFunctor : GFunctor := ⟨RegistryRF, inferInstance⟩

structure RegistryCapacity (GF : BundledGFunctors) where
  entries : GhostMapG GF Nat Record RegistryMap

def slot : Nat := 15
def registry : BundledGFunctors := Heap.registry.set slot registryFunctor
theorem registry_other (i : Nat) (h : i ≠ slot) : registry i = Heap.registry i := by
  simp [registry, BundledGFunctors.set, h]
theorem registry_old (i : Nat) (h : i < 15) : registry i = Heap.registry i :=
  registry_other i (by unfold slot; omega)
theorem registry_unused (i : Nat) (h : 16 ≤ i) : registry i = Heap.registry i :=
  registry_other i (by unfold slot; omega)

@[reducible] def registrySlot : ElemG registry RegistryRF := ⟨15, rfl⟩
def registryCapacity : RegistryCapacity registry := ⟨⟨registrySlot⟩⟩
def ledgerCapacity : Tso.Capacity registry := ⟨⟨⟨0, rfl⟩⟩, ⟨⟨1, rfl⟩⟩⟩
def heapCapacity : Heap.Capacity registry :=
  ⟨ledgerCapacity, ⟨⟨13, rfl⟩⟩, ⟨14, rfl⟩⟩
def capacity : Capacity registry :=
  ⟨heapCapacity, ⟨⟨⟨6, rfl⟩⟩⟩,
    ⟨{ elemG := ⟨7, rfl⟩ }, { elemG := ⟨8, rfl⟩ }, { elemG := ⟨9, rfl⟩ }⟩,
    ⟨⟨⟨12, rfl⟩⟩⟩, ⟨⟨⟨10, rfl⟩⟩⟩,
    ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨⟨4, rfl⟩⟩, ⟨5, rfl⟩⟩⟩
def powerCapacity : PowerGhost.Capacity registry :=
  ⟨⟨3, rfl⟩, { elemG := ⟨11, rfl⟩ }⟩

variable {GF : BundledGFunctors} (registryCap : RegistryCapacity GF)

def registryAuth (name : GName) (entries : RegistryMap Record) : IProp GF :=
  letI := registryCap.entries
  ghost_map_auth name (.own 1) entries

def registered (name : GName) (generation : Nat) (era : Record) : IProp GF :=
  letI := registryCap.entries
  ghost_map_elem name .discard generation era

end MachCSL.Logic.Era
