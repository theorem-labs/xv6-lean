import MachCSL.Logic.FsBlockGhostProofs
import MachCSL.Logic.IcacheTopRegistryLink

namespace MachCSL.Logic.FsBlockGhost
open Iris
open scoped MachCSL.Logic.FsBlockGhost.Key

def registry : BundledGFunctors :=
  ((IcacheTopRegistry.registry.set 39 cacheFunctor).set 40 dirtyFunctor).set 41 exceptionFunctor

theorem registry_old (i : Nat) (bound : i < 39) : registry i = IcacheTopRegistry.registry i := by
  simp [registry, BundledGFunctors.set, show i ≠ 39 by omega, show i ≠ 40 by omega, show i ≠ 41 by omega]
theorem registry_unused (i : Nat) (bound : 42 ≤ i) : registry i = IcacheTopRegistry.registry i := by
  simp [registry, BundledGFunctors.set, show i ≠ 39 by omega, show i ≠ 40 by omega, show i ≠ 41 by omega]

def registryCapacity : IcacheEscrowTokens.Capacity registry :=
  ⟨⟨⟨35, rfl⟩⟩, ⟨36, rfl⟩, ⟨⟨37, rfl⟩⟩, ⟨3, rfl⟩⟩
def epochCapacity : LogEpoch.Capacity registry := ⟨⟨3, rfl⟩, ⟨34, rfl⟩⟩
def transactionCapacity : LogTx.Capacity registry := ⟨⟨⟨33, rfl⟩⟩⟩
def typeCapacity : IcacheTypeGhost.Capacity registry := ⟨⟨32, rfl⟩⟩
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
theorem type_slot : typeCapacity.type.τ = 32 := rfl
theorem tx_slot : transactionCapacity.transactions.elem.τ = 33 := rfl
theorem epoch_slot : epochCapacity.epoch.τ = 3 := rfl
theorem logged_slot : epochCapacity.logged.τ = 34 := rfl

theorem registry_slot : registryCapacity.registry.elem.τ = 35 := rfl
theorem ticket_slot : registryCapacity.ticket.τ = 36 := rfl
theorem corpse_slot : registryCapacity.corpse.elem.τ = 37 := rfl
theorem mono_same : registryCapacity.mono = epochCapacity.epoch := rfl

def topRegistryCapacity : IcacheTopRegistry.Capacity registry := ⟨⟨⟨38, rfl⟩⟩, topCapacity, transactionCapacity⟩
theorem arm_slot : topRegistryCapacity.arms.elem.τ = 38 := rfl
theorem native_top_same : topRegistryCapacity.top = topCapacity := rfl
theorem native_transactions_same : topRegistryCapacity.transactions = transactionCapacity := rfl

theorem topRegistrySpec [InvGS registry] : IcacheTopRegistry.Spec topRegistryCapacity := IcacheTopRegistry.actual topRegistryCapacity
theorem escrowSpec : IcacheEscrowTokens.Spec registryCapacity := IcacheEscrowTokens.actual registryCapacity
theorem epochSpec : LogEpoch.Spec epochCapacity := LogEpoch.actual epochCapacity
theorem transactionSpec : LogTx.Spec transactionCapacity := LogTx.actual transactionCapacity
theorem typeSpec : IcacheTypeGhost.Spec typeCapacity := IcacheTypeGhost.actual typeCapacity
theorem referenceSpec : IcacheRefLedger.Spec referenceCapacity := IcacheRefLedger.actual referenceCapacity
theorem couplingSpec : IcacheCoupling.Spec couplingCapacity := IcacheCoupling.actual couplingCapacity
theorem recordSpec : FsInodeRegion.Spec recordCapacity := FsInodeRegion.actual recordCapacity
theorem heldSetSpec : LockSet.LockSetSpec heldSetCapacity := LockSet.actual heldSetCapacity
theorem lockSpec : Lock.LockSpec lockCapacity := Lock.actual lockCapacity
theorem topSpec : FsTop.FsTopSpec topCapacity := FsTop.actual topCapacity


def nativeCapacity : Capacity registry := ⟨⟨⟨39, rfl⟩⟩, ⟨⟨40, rfl⟩⟩, ⟨⟨41, rfl⟩⟩⟩
/-- The logged view and physical disk use the same existing byte camera. -/
def diskCapacity : Disk.Capacity registry := ⟨⟨⟨12, rfl⟩⟩⟩
theorem cache_slot : nativeCapacity.cache.elem.τ = 39 := rfl
theorem dirty_slot : nativeCapacity.dirty.elem.τ = 40 := rfl
theorem exceptions_slot : nativeCapacity.exceptions.elem.τ = 41 := rfl
theorem disk_machine_same : diskCapacity = machineCapacity.era.disk := rfl
theorem disk_slot : diskCapacity.image.elem.τ = 12 := rfl
theorem nativeSpec : Spec nativeCapacity := actual nativeCapacity

end MachCSL.Logic.FsBlockGhost
