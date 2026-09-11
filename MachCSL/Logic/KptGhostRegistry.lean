import MachCSL.Logic.KptGhostDefs
import MachCSL.Logic.SupervisorBitsRegistry

namespace MachCSL.Logic.KptGhost
open Iris
open scoped MachCSL.Logic.FsBlockGhost.Key

/-- Extend the frozen family at three new, explicit indices. All pre-existing
capacity witnesses below are reconstructed from their original indices. -/
def registry : BundledGFunctors :=
  ((SupervisorBits.registry.set Slot.mapping.index mapFunctor).set
    Slot.tree.index treeFunctor).set Slot.bound.index boundFunctor

theorem registry_other (i : Nat) (hm : i ≠ 45) (ht : i ≠ 46) (hb : i ≠ 47) :
    registry i = SupervisorBits.registry i := by
  simp [registry, BundledGFunctors.set, Slot.index, hm, ht, hb]
theorem registry_old (i : Nat) (old : i < 45) : registry i = SupervisorBits.registry i :=
  registry_other i (by omega) (by omega) (by omega)
theorem registry_unused (i : Nat) (unused : 48 ≤ i) : registry i = SupervisorBits.registry i :=
  registry_other i (by omega) (by omega) (by omega)

/-- Transport any old slot witness, including unnamed client capacities. -/
@[reducible] def preserveOld {F : COFE.OFunctorPre} [RFunctorContractive F]
    (e : ElemG SupervisorBits.registry F) (old : e.τ < 45) : ElemG registry F :=
  ⟨e.τ, (registry_old e.τ old).trans e.transp⟩

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
def crashCapacity : FsCrash.Capacity registry :=
  ⟨⟨42, rfl⟩, { elemG := ⟨43, rfl⟩ }, eraRegistryCapacity, ⟨3, rfl⟩,
    lockCapacity, diskCapacity, linkCapacity, topCapacity⟩
def bootCapacity : FsBootRecovery.Capacity registry := ⟨eraCapacity, blockCapacity⟩
def crashBootstrapCapacity : FsCrash.BootstrapCapacity registry := ⟨crashCapacity, bootCapacity, rfl⟩

theorem history_slot : crashCapacity.history.τ = 42 := rfl
theorem mirror_slot : crashCapacity.mirror.elemG.τ = 43 := rfl
theorem registry_same : crashCapacity.registry = machineCapacity.registry := rfl
theorem counter_same : crashCapacity.mono = machineCapacity.power.sharedNat := rfl
theorem physical_disk_same : crashCapacity.disk = machineCapacity.era.disk := rfl
theorem durable_link_same : crashCapacity.links = linkCapacity := rfl
theorem durable_top_same : crashCapacity.tops = topRegistryCapacity.top := rfl
theorem boot_era_same : crashBootstrapCapacity.boot.era = machineCapacity.era := rfl
theorem boot_disk_same : crashBootstrapCapacity.boot.bytes.bytes = crashCapacity.disk := rfl
theorem cache_slot : blockCapacity.cache.elem.τ = 39 := rfl
theorem dirty_slot : blockCapacity.dirty.elem.τ = 40 := rfl
theorem exceptions_slot : blockCapacity.exceptions.elem.τ = 41 := rfl


@[reducible] def bitSlot : ElemG registry SupervisorBits.BitRF := ⟨44, rfl⟩
def supervisorCapacity : SupervisorBits.Capacity registry := ⟨eraCapacity.registers, { elemG := bitSlot }⟩
theorem bit_slot : supervisorCapacity.bits.elemG.τ = 44 := rfl
theorem physical_registers_same : supervisorCapacity.registers = machineCapacity.era.registers := rfl


@[reducible] def mappingSlot : ElemG registry MapRF := ⟨45, rfl⟩
@[reducible] def treeSlot : ElemG registry TreeRF := ⟨46, rfl⟩
@[reducible] def boundSlot : ElemG registry BoundRF := ⟨47, rfl⟩
def kptCapacity : Capacity registry :=
  ⟨⟨mappingSlot⟩, treeSlot, boundSlot, eraCapacity.views⟩

theorem mapping_slot : kptCapacity.mapping.elem.τ = 45 := rfl
theorem tree_slot : kptCapacity.tree.τ = 46 := rfl
theorem bound_slot : kptCapacity.bound.τ = 47 := rfl
theorem view_slot : kptCapacity.views.views.τ = 2 := rfl
theorem log_slot : kptCapacity.views.sharedNat.τ = 3 := rfl
theorem views_same : kptCapacity.views = machineCapacity.era.views := rfl
theorem log_counter_same : kptCapacity.views.sharedNat = machineCapacity.power.sharedNat := rfl

end MachCSL.Logic.KptGhost
