import MachCSL.Logic.UartGhostDefs
import MachCSL.Logic.InvariantRegistry

namespace MachCSL.Logic.UartGhost
open Iris

def listFunctor : GFunctor := ⟨ListRF, inferInstance⟩
def txFunctor : GFunctor := ⟨constOF (DFracAgree.DFracAgreeR (DiscreteO (List MachCSL.Memory.Byte))), inferInstance⟩
def dlabFunctor : GFunctor := ⟨DlabRF, inferInstance⟩

inductive Slot where
  | traces | transmitter | dlab
  deriving DecidableEq

def Slot.index : Slot → Nat
  | .traces => 20
  | .transmitter => 21
  | .dlab => 22

theorem Slot.index_injective {a b : Slot} (same : a.index = b.index) : a = b := by
  cases a <;> cases b <;> simp_all [index]

def registry : BundledGFunctors :=
  ((Invariant.registry.set Slot.traces.index listFunctor).set Slot.transmitter.index txFunctor).set
    Slot.dlab.index dlabFunctor

theorem registry_old (i : Nat) (bound : i < 20) : registry i = Invariant.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 20 by omega,
    show i ≠ 21 by omega, show i ≠ 22 by omega]

theorem registry_unused (i : Nat) (bound : 23 ≤ i) : registry i = Invariant.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, show i ≠ 20 by omega,
    show i ≠ 21 by omega, show i ≠ 22 by omega]

@[reducible] def traceSlot : ElemG registry ListRF := ⟨20, rfl⟩
@[reducible] def txSlot : ElemG registry (constOF (DFracAgree.DFracAgreeR (DiscreteO (List MachCSL.Memory.Byte)))) := ⟨21, rfl⟩
@[reducible] def dlabSlot : ElemG registry DlabRF := ⟨22, rfl⟩

def registryCapacity : Capacity registry := ⟨⟨traceSlot⟩, { elemG := txSlot }, dlabSlot⟩

/-- The allocated invariant names are reused with the explicit unchanged 16–19 witnesses. -/
def invariantCapacity : Invariant.Capacity registry :=
  ⟨⟨16, rfl⟩, ⟨17, rfl⟩, ⟨18, rfl⟩, ⟨19, rfl⟩⟩

@[reducible] def nativeInvariant (names : Invariant.Names) : InvGS registry := names.native invariantCapacity

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


theorem machine_observation_slot : machineCapacity.observations.elemG.τ = 11 := rfl

end MachCSL.Logic.UartGhost
