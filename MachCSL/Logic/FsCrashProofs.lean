import MachCSL.Logic.FsCrashArmProofs
import MachCSL.Logic.FsDurReadbackProofs
import MachCSL.Logic.FsBootRecoveryProofs

namespace MachCSL.Logic.FsCrash
open Iris Iris.Std Iris.Algebra Iris.BI MachCSL.Memory
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance Pfs_timeless names covered start disk : Timeless (Pfs capacity names covered start disk) := by
  unfold Pfs; infer_instance
instance named_timeless swap registry started covered start disk : Timeless (named capacity swap registry started covered start disk) := by
  unfold named; infer_instance
instance lend_timeless covered start disk : Timeless (lend capacity covered start disk) := by
  unfold lend; infer_instance

theorem recovers names covered start disk : Pfs capacity names covered start disk ⊢
    ⌜∃ committed history, Xv6.Fs.Recovery.Recovers (Xv6.Fs.blocks disk) committed covered start ∧
      history ≠ [] ∧ history.getLast? = some committed⌝ := by
  unfold Pfs
  iintro ⟨%record, _, %wf, _, _⟩
  ipureintro
  exact ⟨record.committed, record.history, wf.recovery, record_history_nonempty _ _ _ _ wf, wf.last⟩

theorem receipt_committed names covered start disk committed :
    Pfs capacity names covered start disk ∗ receipt capacity names committed ⊢
      ⌜∃ record, RecordWF record (Xv6.Fs.blocks disk) covered start ∧ committed ∈ record.history⌝ := by
  unfold Pfs receipt
  iintro ⟨⟨%record, Hh, %wf, _, _⟩, ⟨%pre, Hl⟩⟩
  ihave %historyPrefix := history_valid capacity names.history record.history (pre ++ [committed]) $$ [$Hh $Hl]
  ipureintro
  exact ⟨record, wf, historyPrefix.mem (by simp)⟩

theorem header_keep names covered start disk : Pfs capacity names covered start disk ⊢
    ⌜Xv6.Fs.Recovery.HeaderWF (Xv6.Fs.blocks disk) covered start⌝ ∗ Pfs capacity names covered start disk := by
  unfold Pfs
  iintro ⟨%record, Hh, %wf, Harm, Hdur⟩
  isplit
  · ipureintro; exact wf.header
  · iexists record
    iframe Hh Harm Hdur
    ipureintro; exact wf

theorem commit_receipt names covered start disk : Pfs capacity names covered start disk ⊢
    ∃ (committed : BlockMap) (state : Xv6.Fs.DurableState.State),
      ⌜Xv6.Fs.Recovery.Recovers (Xv6.Fs.blocks disk) committed covered start⌝ ∗
      ⌜Xv6.Fs.Snapshot.OK state committed⌝ ∗ Pfs capacity names covered start disk := by
  unfold Pfs
  iintro ⟨%record, Hh, %wf, Harm, Hdur⟩
  have full := Xv6.Fs.Recovery.recovery_disk_full _ _ _ _ wf.recovery
  ihave ⟨%state, %ok, Hdur⟩ := FsDurReadback.P_dur_tie_keep capacity.disk capacity.links capacity.tops
    record.committed full $$ Hdur
  iexists record.committed, state
  isplit
  · ipureintro; exact wf.recovery
  · isplit
    · ipureintro; exact ok
    · iexists record
      iframe Hh Harm Hdur
      ipureintro; exact wf

theorem bank names covered start disk : Pfs capacity names covered start disk ⊢
    ∃ committed : BlockMap, receipt capacity names committed ∗
      ⌜Xv6.Fs.Snapshot.Holds committed⌝ ∗ Pfs capacity names covered start disk := by
  unfold Pfs
  iintro ⟨%record, Hh, %wf, Harm, Hdur⟩
  have full := Xv6.Fs.Recovery.recovery_disk_full _ _ _ _ wf.recovery
  ihave ⟨%state, %ok, Hdur⟩ := FsDurReadback.P_dur_tie_keep capacity.disk capacity.links capacity.tops
    record.committed full $$ Hdur
  ihave ⟨Hh, #Hlb⟩ := history_snapshot capacity names.history record.history $$ Hh
  obtain ⟨pre, same⟩ := history_last_split _ _ _ _ wf
  iexists record.committed
  isplitl []
  · unfold receipt
    iexists pre
    isimp only [same] at Hlb
    iexact Hlb
  · isplit
    · ipureintro; exact ⟨state, ok⟩
    · iexists record
      iframe Hh Harm Hdur
      ipureintro; exact wf

theorem durable_accessor names covered start disk : Pfs capacity names covered start disk ⊢
    ∃ committed : BlockMap, ⌜Xv6.Fs.Recovery.Recovers (Xv6.Fs.blocks disk) committed covered start⌝ ∗
      FsDurSnapshot.Pdur capacity.disk capacity.links capacity.tops committed ∗
      (FsDurSnapshot.Pdur capacity.disk capacity.links capacity.tops committed -∗ Pfs capacity names covered start disk) := by
  unfold Pfs
  iintro ⟨%record, Hh, %wf, Harm, Hdur⟩
  iexists record.committed
  iframe Hdur
  isplit
  · ipureintro; exact wf.recovery
  · iintro Hdur
    iexists record
    iframe Hh Harm Hdur
    ipureintro; exact wf

theorem of_durable swap registry started disk committed covered start
    (recovery : Xv6.Fs.Recovery.Recovers (Xv6.Fs.blocks disk) committed covered start)
    (wf : Xv6.Fs.Recovery.HeaderWF (Xv6.Fs.blocks disk) covered start) (frame : IProp GF) :
    iprop(⊢ FsDurSnapshot.Pdur capacity.disk capacity.links capacity.tops committed -∗
      counterAuth capacity swap 0 -∗ frame ==∗ ∃ names : Names,
      ⌜names.swap = swap ∧ names.registry = registry ∧ names.started = started⌝ ∗
      Pfs capacity names covered start disk ∗ receipt capacity names committed ∗ frame) := by
  iintro Hdur Hswap Hframe
  imod history_allocate capacity [committed] frame $$ Hframe with ⟨%historyName, Hh, #Hlb, Hframe⟩
  let names : Names := ⟨historyName, swap, registry, started⟩
  ihave Harm := arm_at_rest capacity names covered start disk $$ Hswap
  imodintro
  iexists names
  iframe Hframe
  isplit
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  · isplitl [Hh Harm Hdur]
    · unfold Pfs
      iexists (⟨committed, [committed]⟩ : Record)
      iframe Hh Harm Hdur
      ipureintro
      exact ⟨recovery, rfl, wf⟩
    · unfold receipt
      iexists ([] : List BlockMap)
      dsimp only [names, List.nil_append]
      iexact Hlb

theorem actual : Spec capacity :=
  ⟨recovers capacity, receipt_committed capacity, header_keep capacity, commit_receipt capacity,
    bank capacity, durable_accessor capacity, of_durable capacity⟩

variable {hlc : HasLC} [InvGS_gen hlc GF]

theorem bootstrap (capacity : BootstrapCapacity GF) crashNames template era memory state length covered start device link top
    (bound : Xv6.Fs.CovIn covered length) (E : CoPset) (frame : IProp GF) :
    iprop(⊢ Pfs capacity.crash crashNames covered start state.devices.virtio.v_disk -∗
      Era.interp capacity.boot.era era state -∗ Era.bootClients capacity.boot.era era memory state length -∗
      frame ={E}=∗ ∃ names : FsBootRecovery.Names,
      ⌜FsBootRecovery.Facts state.devices.virtio.v_disk covered start⌝ ∗
      Pfs capacity.crash crashNames covered start state.devices.virtio.v_disk ∗
      Era.interp capacity.boot.era era state ∗ FsBootRecovery.otherClients capacity.boot era memory state ∗
      FsBootRecovery.allocated capacity.boot (FsBootRecovery.forEra template era) state.devices.virtio.v_disk
        covered start device link top names ∗
      FsBootBytes.remainder capacity.boot.bytes (FsBootRecovery.forEra template era)
        state.devices.virtio.v_disk length covered ∗ frame) := by
  iintro Hp Hera Hclients Hframe
  ihave ⟨%wf, Hp⟩ := header_keep capacity.crash crashNames covered start state.devices.virtio.v_disk $$ Hp
  imod FsBootRecovery.era_boot_ghosts capacity.boot template era memory state length covered start device link top bound wf E
    (iprop(Pfs capacity.crash crashNames covered start state.devices.virtio.v_disk ∗ frame))
    $$ Hera Hclients [$Hp $Hframe] with ⟨%names, %facts, Hera, Hother, Halloc, Hrest, Hp, Hframe⟩
  imodintro
  iexists names
  iframe
  ipureintro; exact facts

theorem bootstrapSpec (capacity : BootstrapCapacity GF) : BootstrapSpec capacity := ⟨bootstrap capacity⟩

end MachCSL.Logic.FsCrash
