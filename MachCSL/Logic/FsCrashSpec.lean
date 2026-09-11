import MachCSL.Logic.FsCrashDefs

namespace MachCSL.Logic.FsCrash
open Iris Iris.Std Iris.Algebra Iris.BI MachCSL.Memory

structure HistorySpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  allocate : ∀ history (frame : IProp GF),
    iprop(frame ⊢ |==> ∃ name : GName, historyAuth capacity name history ∗ historyLowerBound capacity name history ∗ frame)
  snapshot : ∀ name history, historyAuth capacity name history ⊢
    historyAuth capacity name history ∗ historyLowerBound capacity name history
  valid : ∀ name history pre, historyAuth capacity name history ∗ historyLowerBound capacity name pre ⊢
    ⌜pre <+: history⌝
  update : ∀ name history next, history <+: next →
    iprop(⊢ historyAuth capacity name history ==∗ historyAuth capacity name next)
  boot_allocate : ∀ frame : IProp GF, iprop(frame ⊢ |==> ∃ name : GName, bootToken capacity name ∗ frame)
  boot_exclusive : ∀ name, bootToken capacity name ∗ bootToken capacity name ⊢ False

structure ArmSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  at_rest : ∀ names covered start disk,
    counterAuth capacity names.swap 0 ⊢ arm capacity names covered start disk
  custody_started : ∀ names covered start disk generation,
    custody capacity names covered start disk generation ⊢
      started capacity names generation ∗ custody capacity names covered start disk generation
  upper_bound : ∀ names covered start disk generation n count, n = generation + 1 →
    counterAuth capacity names.started n ∗ armBranch capacity names covered start disk count ⊢
      ⌜count ≤ generation + 1⌝ ∗ counterAuth capacity names.started n ∗ armBranch capacity names covered start disk count
  swap : ∀ names covered start disk next generation era n mirror,
    n = generation + 1 → MirrorOK mirror (Xv6.Fs.blocks next) covered start →
    iprop(⊢ registered capacity names generation era -∗ started capacity names generation -∗
      counterAuth capacity names.started n -∗ mirrorHalf capacity era.logMirror mirror -∗
      arm capacity names covered start disk ==∗ arm capacity names covered start next ∗
      counterAuth capacity names.started n ∗ counterLowerBound capacity names.swap (generation + 1))
  accessor : ∀ names covered start disk generation era n mirror,
    n = generation + 1 →
    iprop(⊢ registered capacity names generation era -∗ counterLowerBound capacity names.swap (generation + 1) -∗
      counterAuth capacity names.started n -∗ mirrorHalf capacity era.logMirror mirror -∗
      arm capacity names covered start disk -∗
      ⌜MirrorOK mirror (Xv6.Fs.blocks disk) covered start⌝ ∗ counterAuth capacity names.started n ∗
      (∀ (next : Physical) (newMirror : LogMirror),
        ⌜MirrorOK newMirror (Xv6.Fs.blocks next) covered start⌝ ==∗
        arm capacity names covered start next ∗ mirrorHalf capacity era.logMirror newMirror))

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  recovers : ∀ names covered start disk, Pfs capacity names covered start disk ⊢
    ⌜∃ committed history, Xv6.Fs.Recovery.Recovers (Xv6.Fs.blocks disk) committed covered start ∧
      history ≠ [] ∧ history.getLast? = some committed⌝
  receipt_committed : ∀ names covered start disk committed,
    Pfs capacity names covered start disk ∗ receipt capacity names committed ⊢
      ⌜∃ record, RecordWF record (Xv6.Fs.blocks disk) covered start ∧ committed ∈ record.history⌝
  header_keep : ∀ names covered start disk, Pfs capacity names covered start disk ⊢
    ⌜Xv6.Fs.Recovery.HeaderWF (Xv6.Fs.blocks disk) covered start⌝ ∗ Pfs capacity names covered start disk
  commit_receipt : ∀ names covered start disk, Pfs capacity names covered start disk ⊢
    ∃ (committed : BlockMap) (state : Xv6.Fs.DurableState.State),
      ⌜Xv6.Fs.Recovery.Recovers (Xv6.Fs.blocks disk) committed covered start⌝ ∗
      ⌜Xv6.Fs.Snapshot.OK state committed⌝ ∗ Pfs capacity names covered start disk
  bank : ∀ names covered start disk, Pfs capacity names covered start disk ⊢
    ∃ committed : BlockMap, receipt capacity names committed ∗
      ⌜Xv6.Fs.Snapshot.Holds committed⌝ ∗ Pfs capacity names covered start disk
  durable_accessor : ∀ names covered start disk, Pfs capacity names covered start disk ⊢
    ∃ committed : BlockMap, ⌜Xv6.Fs.Recovery.Recovers (Xv6.Fs.blocks disk) committed covered start⌝ ∗
      FsDurSnapshot.Pdur capacity.disk capacity.links capacity.tops committed ∗
      (FsDurSnapshot.Pdur capacity.disk capacity.links capacity.tops committed -∗ Pfs capacity names covered start disk)
  of_durable : ∀ swap registry started disk committed covered start,
    Xv6.Fs.Recovery.Recovers (Xv6.Fs.blocks disk) committed covered start →
    Xv6.Fs.Recovery.HeaderWF (Xv6.Fs.blocks disk) covered start →
    ∀ frame : IProp GF,
    iprop(⊢ FsDurSnapshot.Pdur capacity.disk capacity.links capacity.tops committed -∗
      counterAuth capacity swap 0 -∗ frame ==∗ ∃ names : Names,
      ⌜names.swap = swap ∧ names.registry = registry ∧ names.started = started⌝ ∗
      Pfs capacity names covered start disk ∗ receipt capacity names committed ∗ frame)

structure BootstrapSpec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : BootstrapCapacity GF) : Prop where
  boot : ∀ crashNames template era memory state length covered start device link top,
    Xv6.Fs.CovIn covered length → ∀ (E : CoPset) (frame : IProp GF),
    iprop(⊢ Pfs capacity.crash crashNames covered start state.devices.virtio.v_disk -∗
      Era.interp capacity.boot.era era state -∗ Era.bootClients capacity.boot.era era memory state length -∗
      frame ={E}=∗ ∃ names : FsBootRecovery.Names,
      ⌜FsBootRecovery.Facts state.devices.virtio.v_disk covered start⌝ ∗
      Pfs capacity.crash crashNames covered start state.devices.virtio.v_disk ∗
      Era.interp capacity.boot.era era state ∗ FsBootRecovery.otherClients capacity.boot era memory state ∗
      FsBootRecovery.allocated capacity.boot (FsBootRecovery.forEra template era) state.devices.virtio.v_disk
        covered start device link top names ∗
      FsBootBytes.remainder capacity.boot.bytes (FsBootRecovery.forEra template era)
        state.devices.virtio.v_disk length covered ∗ frame)

end MachCSL.Logic.FsCrash
