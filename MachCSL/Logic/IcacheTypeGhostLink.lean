import MachCSL.Logic.IcacheTypeGhostProofs
import MachCSL.Logic.IcacheRefLedgerLink

namespace MachCSL.Logic.IcacheTypeGhost
open Iris

/-- The exact non-unital type one-shot occupies slot 32. Separate ghost
names carry inode generations and the source boot-shelter regime. -/
def registry : BundledGFunctors := IcacheRefLedger.registry.set 32 typeFunctor

theorem registry_old (i : Nat) (bound : i < 32) : registry i = IcacheRefLedger.registry i := by
  simp [registry, BundledGFunctors.set, show i ≠ 32 by omega]
theorem registry_unused (i : Nat) (bound : 33 ≤ i) : registry i = IcacheRefLedger.registry i := by
  simp [registry, BundledGFunctors.set, show i ≠ 32 by omega]
@[reducible] def typeSlot : ElemG registry TypeRF := ⟨32, rfl⟩
def registryCapacity : Capacity registry := ⟨typeSlot⟩
def referenceCapacity : IcacheRefLedger.Capacity registry := ⟨⟨31, rfl⟩⟩
def couplingCapacity : IcacheCoupling.Capacity registry := ⟨⟨28, rfl⟩, ⟨29, rfl⟩, ⟨30, rfl⟩⟩
def recordCapacity : FsInodeRegion.Capacity registry := ⟨⟨⟨27, rfl⟩⟩⟩
def heldSetCapacity : LockSet.Capacity registry := ⟨⟨26, rfl⟩⟩
def topCapacity : FsTop.Capacity registry := ⟨⟨⟨25, rfl⟩⟩⟩
def lockCapacity : Lock.Capacity registry := ⟨⟨24, rfl⟩⟩
def linkCapacity : FsLink.Capacity registry := ⟨⟨23, rfl⟩⟩

def uartCapacity : UartGhost.Capacity registry :=
  ⟨⟨⟨20, rfl⟩⟩, { elemG := ⟨21, rfl⟩ }, ⟨22, rfl⟩⟩
def invariantCapacity : Invariant.Capacity registry :=
  ⟨⟨16, rfl⟩, ⟨17, rfl⟩, ⟨18, rfl⟩, ⟨19, rfl⟩⟩
@[reducible] def nativeInvariant (names : Invariant.Names) : InvGS registry :=
  names.native invariantCapacity

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
theorem top_slot : topCapacity.top.elem.τ = 25 := rfl
theorem lock_slot : lockCapacity.lock.τ = 24 := rfl
theorem link_slot : linkCapacity.link.τ = 23 := rfl
theorem held_set_slot : heldSetCapacity.set.τ = 26 := rfl
theorem record_slot : recordCapacity.record.elem.τ = 27 := rfl
theorem count_slot : couplingCapacity.count.τ = 28 := rfl
theorem mirror_slot : couplingCapacity.mirror.τ = 29 := rfl
theorem pin_slot : couplingCapacity.pin.τ = 30 := rfl

theorem reference_slot : referenceCapacity.ledger.τ = 31 := rfl
theorem type_slot : registryCapacity.type.τ = 32 := rfl

theorem registrySpec : Spec registryCapacity := actual registryCapacity
theorem referenceSpec : IcacheRefLedger.Spec referenceCapacity := IcacheRefLedger.actual referenceCapacity
theorem couplingSpec : IcacheCoupling.Spec couplingCapacity := IcacheCoupling.actual couplingCapacity
theorem recordSpec : FsInodeRegion.Spec recordCapacity := FsInodeRegion.actual recordCapacity
theorem heldSetSpec : LockSet.LockSetSpec heldSetCapacity := LockSet.actual heldSetCapacity
theorem lockSpec : Lock.LockSpec lockCapacity := Lock.actual lockCapacity
theorem topSpec : FsTop.FsTopSpec topCapacity := FsTop.actual topCapacity

end MachCSL.Logic.IcacheTypeGhost
