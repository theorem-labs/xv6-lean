import MachCSL.Logic.TsoDefs
import Iris.Instances.Lib.GhostMap
import Iris.Std.HeapInstances

/-!
The first two actual resource slots for the TSO byte ledger. This is a partial
registry, not the full source `tsoMemΣ` or `gen_heapΣ`: the first slot is exactly
the value-map component of gen_heap, with its metadata slots still outstanding;
the second is `TsoGhost.tsomem_tsG`. Runtime names are allocated separately.
-/
namespace MachCSL.Logic.Tso
open MachCSL.Memory Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

abbrev AddressMap (V : Type) := _root_.Std.ExtTreeMap PhysicalAddress V
abbrev ByteRA := HeapView PhysicalAddress (Agree (DiscreteO Byte)) AddressMap
abbrev TimestampRA := HeapView PhysicalAddress (Agree (DiscreteO TimestampElem)) AddressMap

def byteFunctor : GFunctor := ⟨constOF ByteRA, inferInstance⟩
def timestampFunctor : GFunctor := ⟨constOF TimestampRA, inferInstance⟩

inductive Slot where
  | physicalBytes
  | timestamps
  deriving DecidableEq

def Slot.index : Slot → Nat
  | .physicalBytes => 0
  | .timestamps => 1

theorem Slot.index_injective {a b : Slot} (h : a.index = b.index) : a = b := by
  cases a <;> cases b <;> simp_all [index]

def registry : BundledGFunctors :=
  (BundledGFunctors.default.set Slot.physicalBytes.index byteFunctor).set
    Slot.timestamps.index timestampFunctor

theorem registry_unused (i : Nat) (h : 2 ≤ i) : registry i = BundledGFunctors.default i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 0 by omega, show i ≠ 1 by omega]

@[reducible] def byteSlot : ElemG registry (constOF ByteRA) := ⟨0, rfl⟩
@[reducible] def timestampSlot : ElemG registry (constOF TimestampRA) := ⟨1, rfl⟩

/-- Capacity is explicit data, never an assumed initialized ownership assertion. -/
structure Capacity (GF : BundledGFunctors) where
  bytes : GhostMapG GF PhysicalAddress Byte AddressMap
  timestamps : GhostMapG GF PhysicalAddress TimestampElem AddressMap

def registryCapacity : Capacity registry := ⟨⟨byteSlot⟩, ⟨timestampSlot⟩⟩

/-- These names may be equal numerically: the explicitly distinct slots disambiguate them. -/
structure Names where
  bytes : GName
  timestamps : GName

section Ownership
variable {GF : BundledGFunctors} (capacity : Capacity GF)

abbrev byteAuth (γ : GName) (dq : DFrac) (memory : AddressMap Byte) : IProp GF :=
  letI := capacity.bytes
  ghost_map_auth γ dq memory

abbrev byteElem (γ : GName) (dq : DFrac) (a : PhysicalAddress) (byte : Byte) : IProp GF :=
  letI := capacity.bytes
  ghost_map_elem γ dq a byte

abbrev timestampAuth (γ : GName) (dq : DFrac) (timestamps : AddressMap TimestampElem) : IProp GF :=
  letI := capacity.timestamps
  ghost_map_auth γ dq timestamps

abbrev timestampElem (γ : GName) (dq : DFrac) (a : PhysicalAddress) (e : TimestampElem) : IProp GF :=
  letI := capacity.timestamps
  ghost_map_elem γ dq a e

/-- The source's per-element interpretation, without concealing any payload premise. -/
def TimestampMapOK (image memory : ByteMap 64) (log : WriteLog 64)
    (timestamps : AddressMap TimestampElem) : Prop :=
  ∀ a e, timestamps[a]? = some e → TimestampOK image memory log a e

end Ownership
end MachCSL.Logic.Tso
