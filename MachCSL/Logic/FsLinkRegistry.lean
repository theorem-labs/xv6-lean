import MachCSL.Logic.FsLinkDefs
import MachCSL.Logic.UartGhostRegistry

namespace MachCSL.Logic.FsLink
open Iris

def linkFunctor : GFunctor := ⟨LinkRF, inferInstance⟩
def registry : BundledGFunctors := UartGhost.registry.set 23 linkFunctor

theorem registry_old (i : Nat) (bound : i < 23) : registry i = UartGhost.registry i := by
  simp [registry, BundledGFunctors.set, show i ≠ 23 by omega]

theorem registry_unused (i : Nat) (bound : 24 ≤ i) : registry i = UartGhost.registry i := by
  simp [registry, BundledGFunctors.set, show i ≠ 23 by omega]

@[reducible] def linkSlot : ElemG registry LinkRF := ⟨23, rfl⟩
def registryCapacity : Capacity registry := ⟨linkSlot⟩

def uartCapacity : UartGhost.Capacity registry :=
  ⟨⟨⟨20, rfl⟩⟩, { elemG := ⟨21, rfl⟩ }, ⟨22, rfl⟩⟩
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
theorem observation_slot : machineCapacity.observations.elemG.τ = 11 := rfl
theorem link_slot : registryCapacity.link.τ = 23 := rfl

end MachCSL.Logic.FsLink
