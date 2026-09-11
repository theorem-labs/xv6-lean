import MachCSL.Logic.FsCrashProofs
import MachCSL.Logic.FsBootRecoveryLink

namespace MachCSL.Logic.FsCrash
open Iris
open scoped MachCSL.Logic.FsBlockGhost.Key

/-- Source fsCrash history and fixed-layer mirror extend the existing world. -/
def registry : BundledGFunctors := (FsBlockGhost.registry.set 42 historyFunctor).set 43 mirrorFunctor

theorem registry_old (i : Nat) (bound : i < 42) : registry i = FsBlockGhost.registry i := by
  simp [registry, BundledGFunctors.set, show i ≠ 42 by omega, show i ≠ 43 by omega]
theorem registry_unused (i : Nat) (bound : 44 ≤ i) : registry i = FsBlockGhost.registry i := by
  simp [registry, BundledGFunctors.set, show i ≠ 42 by omega, show i ≠ 43 by omega]

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
theorem freeze_mirror_slot : couplingCapacity.mirror.τ = 29 := rfl
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


def blockCapacity : FsBlockGhost.Capacity registry := ⟨⟨⟨39, rfl⟩⟩, ⟨⟨40, rfl⟩⟩, ⟨⟨41, rfl⟩⟩⟩
def diskCapacity : Disk.Capacity registry := ⟨⟨⟨12, rfl⟩⟩⟩
def nativeCapacity : Capacity registry :=
  ⟨⟨42, rfl⟩, { elemG := ⟨43, rfl⟩ }, eraRegistryCapacity, ⟨3, rfl⟩,
    lockCapacity, diskCapacity, linkCapacity, topCapacity⟩
def bootCapacity : FsBootRecovery.Capacity registry := ⟨eraCapacity, blockCapacity⟩
def nativeBootstrapCapacity : BootstrapCapacity registry := ⟨nativeCapacity, bootCapacity, rfl⟩

theorem history_slot : nativeCapacity.history.τ = 42 := rfl
theorem mirror_slot : nativeCapacity.mirror.elemG.τ = 43 := rfl
theorem registry_same : nativeCapacity.registry = machineCapacity.registry := rfl
theorem counter_same : nativeCapacity.mono = machineCapacity.power.sharedNat := rfl
theorem physical_disk_same : nativeCapacity.disk = machineCapacity.era.disk := rfl
theorem durable_link_same : nativeCapacity.links = linkCapacity := rfl
theorem durable_top_same : nativeCapacity.tops = topRegistryCapacity.top := rfl
theorem boot_era_same : nativeBootstrapCapacity.boot.era = machineCapacity.era := rfl
theorem boot_disk_same : nativeBootstrapCapacity.boot.bytes.bytes = nativeCapacity.disk := rfl
theorem cache_slot : blockCapacity.cache.elem.τ = 39 := rfl
theorem dirty_slot : blockCapacity.dirty.elem.τ = 40 := rfl
theorem exceptions_slot : blockCapacity.exceptions.elem.τ = 41 := rfl

theorem nativeHistorySpec : HistorySpec nativeCapacity := historySpec nativeCapacity
theorem nativeArmSpec : ArmSpec nativeCapacity := armSpec nativeCapacity
theorem nativeSpec : Spec nativeCapacity := actual nativeCapacity
theorem nativeBootstrapSpec [InvGS registry] : BootstrapSpec nativeBootstrapCapacity :=
  bootstrapSpec nativeBootstrapCapacity

end MachCSL.Logic.FsCrash
