import MachCSL.Logic.IcacheEscrowTokensProofs
import MachCSL.Logic.LogEpochLink

namespace MachCSL.Logic.IcacheEscrowTokens
open Iris

/-- Exact registry, redemption ticket and corpse cameras from icacheG. -/
def registry : BundledGFunctors :=
  ((LogEpoch.registry.set 35 registryFunctor).set 36 ticketFunctor).set 37 corpseFunctor

theorem registry_old (i : Nat) (bound : i < 35) : registry i = LogEpoch.registry i := by
  simp [registry, BundledGFunctors.set, show i ≠ 35 by omega,
    show i ≠ 36 by omega, show i ≠ 37 by omega]
theorem registry_unused (i : Nat) (bound : 38 ≤ i) : registry i = LogEpoch.registry i := by
  simp [registry, BundledGFunctors.set, show i ≠ 35 by omega,
    show i ≠ 36 by omega, show i ≠ 37 by omega]

def registryCapacity : Capacity registry :=
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

theorem nativeSpec : Spec registryCapacity := actual registryCapacity
theorem epochSpec : LogEpoch.Spec epochCapacity := LogEpoch.actual epochCapacity
theorem transactionSpec : LogTx.Spec transactionCapacity := LogTx.actual transactionCapacity
theorem typeSpec : IcacheTypeGhost.Spec typeCapacity := IcacheTypeGhost.actual typeCapacity
theorem referenceSpec : IcacheRefLedger.Spec referenceCapacity := IcacheRefLedger.actual referenceCapacity
theorem couplingSpec : IcacheCoupling.Spec couplingCapacity := IcacheCoupling.actual couplingCapacity
theorem recordSpec : FsInodeRegion.Spec recordCapacity := FsInodeRegion.actual recordCapacity
theorem heldSetSpec : LockSet.LockSetSpec heldSetCapacity := LockSet.actual heldSetCapacity
theorem lockSpec : Lock.LockSpec lockCapacity := Lock.actual lockCapacity
theorem topSpec : FsTop.FsTopSpec topCapacity := FsTop.actual topCapacity

end MachCSL.Logic.IcacheEscrowTokens
