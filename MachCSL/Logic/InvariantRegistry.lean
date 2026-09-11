import MachCSL.Logic.InvariantDefs

/-! Native invariant machinery at slots 16–19; all application slots remain intact. -/
namespace MachCSL.Logic.Invariant
open Iris

def worldFunctor : GFunctor := ⟨WorldRF, inferInstance⟩
def enabledFunctor : GFunctor := ⟨EnabledRF, inferInstance⟩
def disabledFunctor : GFunctor := ⟨DisabledRF, inferInstance⟩
def creditFunctor : GFunctor := ⟨CreditRF, inferInstance⟩

inductive Slot where
  | world | enabled | disabled | credit
  deriving DecidableEq

def Slot.index : Slot → Nat
  | .world => 16
  | .enabled => 17
  | .disabled => 18
  | .credit => 19

theorem Slot.index_injective {a b : Slot} (h : a.index = b.index) : a = b := by
  cases a <;> cases b <;> simp_all [index]

def registry : BundledGFunctors :=
  (((Era.registry.set Slot.world.index worldFunctor).set Slot.enabled.index enabledFunctor).set
    Slot.disabled.index disabledFunctor).set Slot.credit.index creditFunctor

theorem registry_old (i : Nat) (h : i < 16) : registry i = Era.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 16 by omega,
    show i ≠ 17 by omega, show i ≠ 18 by omega, show i ≠ 19 by omega]

theorem registry_unused (i : Nat) (h : 20 ≤ i) : registry i = Era.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 16 by omega,
    show i ≠ 17 by omega, show i ≠ 18 by omega, show i ≠ 19 by omega]

@[reducible] def worldSlot : ElemG registry WorldRF := ⟨16, rfl⟩
@[reducible] def enabledSlot : ElemG registry EnabledRF := ⟨17, rfl⟩
@[reducible] def disabledSlot : ElemG registry DisabledRF := ⟨18, rfl⟩
@[reducible] def creditSlot : ElemG registry CreditRF := ⟨19, rfl⟩

def registryCapacity : Capacity registry := ⟨worldSlot, enabledSlot, disabledSlot, creditSlot⟩

/-- Explicit native pre-capacity; this value contains no allocated names. -/
@[reducible] def registryPreS : InvGpreS registry := registryCapacity.preS

def ledgerCapacity : Tso.Capacity registry := ⟨⟨⟨0, rfl⟩⟩, ⟨⟨1, rfl⟩⟩⟩
def heapCapacity : Heap.Capacity registry := ⟨ledgerCapacity, ⟨⟨13, rfl⟩⟩, ⟨14, rfl⟩⟩
def eraCapacity : Era.Capacity registry :=
  ⟨heapCapacity, ⟨⟨⟨6, rfl⟩⟩⟩,
    ⟨{ elemG := ⟨7, rfl⟩ }, { elemG := ⟨8, rfl⟩ }, { elemG := ⟨9, rfl⟩ }⟩,
    ⟨⟨⟨12, rfl⟩⟩⟩, ⟨⟨⟨10, rfl⟩⟩⟩,
    ⟨⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨⟨4, rfl⟩⟩, ⟨5, rfl⟩⟩⟩
def eraRegistryCapacity : Era.RegistryCapacity registry := ⟨⟨⟨15, rfl⟩⟩⟩
def machineCapacity : MachineInterp.Capacity registry :=
  ⟨eraCapacity, eraRegistryCapacity, { elemG := ⟨11, rfl⟩ }⟩

theorem machine_byte_same : machineCapacity.era.heap.ledger = ledgerCapacity := rfl
theorem machine_tso_same : machineCapacity.era.tso.ledger = ledgerCapacity := rfl
theorem machine_mono_same : machineCapacity.power.sharedNat = eraCapacity.views.sharedNat := rfl

end MachCSL.Logic.Invariant
