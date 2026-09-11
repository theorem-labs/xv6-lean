import MachCSL.Logic.IcacheRefLedgerBootProofs
import MachCSL.Logic.IcacheCouplingLink

namespace MachCSL.Logic.IcacheRefLedger
open Iris

/-- The inode-reference ledger is separate from FsLink and the three
coupling maps. Its single per-inum-Auth map occupies assigned slot 31. -/
def registry : BundledGFunctors := IcacheCoupling.registry.set 31 ledgerFunctor

theorem registry_old (i : Nat) (bound : i < 31) : registry i = IcacheCoupling.registry i := by
  simp [registry, BundledGFunctors.set, show i ≠ 31 by omega]
theorem registry_unused (i : Nat) (bound : 32 ≤ i) : registry i = IcacheCoupling.registry i := by
  simp [registry, BundledGFunctors.set, show i ≠ 31 by omega]
@[reducible] def ledgerSlot : ElemG registry LedgerRF := ⟨31, rfl⟩
def registryCapacity : Capacity registry := ⟨ledgerSlot⟩
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

theorem ledger_slot : registryCapacity.ledger.τ = 31 := rfl

theorem registrySpec : Spec registryCapacity := actual registryCapacity
theorem couplingSpec : IcacheCoupling.Spec couplingCapacity := IcacheCoupling.actual couplingCapacity
theorem recordSpec : FsInodeRegion.Spec recordCapacity := FsInodeRegion.actual recordCapacity
theorem heldSetSpec : LockSet.LockSetSpec heldSetCapacity := LockSet.actual heldSetCapacity
theorem lockSpec : Lock.LockSpec lockCapacity := Lock.actual lockCapacity
theorem topSpec : FsTop.FsTopSpec topCapacity := FsTop.actual topCapacity

end MachCSL.Logic.IcacheRefLedger
