import MachCSL.Logic.FsCfgSnapSpec
import MachCSL.Logic.FsCrashProofs
import MachCSL.Logic.FsDurSnapshotXferProofs
import Xv6.Fs.SnapshotCoverageProofs

namespace MachCSL.Logic.FsCfgSnap
open Iris Iris.Std Iris.BI Xv6.Fs
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem loan names covered start physical (frame : IProp GF) :
    iprop(⊢ FsCrash.Pfs capacity.crash names covered start physical -∗ frame ==∗
      ⌜Recovery.HeaderWF (blocks physical) covered start⌝ ∗
      FsCrash.Pfs capacity.crash names covered start physical ∗
      FsCrash.lend capacity.crash covered start physical ∗ frame) := by
  iintro Hp Hframe
  ihave ⟨%header, Hp⟩ := FsCrash.header_keep capacity.crash names covered start physical $$ Hp
  ihave ⟨%disk, %recover, Hdur, Hback⟩ :=
    FsCrash.durable_accessor capacity.crash names covered start physical $$ Hp
  imod FsDurSnapshotXfer.P_dur_clone capacity.crash.disk capacity.crash.links capacity.crash.tops disk
    $$ Hdur with ⟨Hdur, Hnew⟩
  ihave Hp := Hback $$ Hdur
  imodintro
  isplit
  · ipureintro; exact header
  isplitl [Hp]
  · iexact Hp
  isplitl [Hnew]
  · unfold FsCrash.lend
    iexists disk
    iframe Hnew
    ipureintro; exact recover
  · iexact Hframe

theorem open_loan covered start physical :
    FsCrash.lend capacity.crash covered start physical ⊢
      ∃ g gl gt state, ⌜Snapshot.OK state (Recovery.recover (blocks physical) covered start)⌝ ∗
        snapshot capacity g gl gt physical covered start state := by
  iintro H
  iunfold FsCrash.lend at H
  icases H with ⟨%disk, %recover, H⟩
  have same : disk = FsBootRecovery.recovered physical covered start := recover
  subst disk
  iunfold FsDurSnapshot.Pdur at H
  icases H with ⟨%g, %gl, %gt, %state, H⟩
  ihave ⟨%ok, H⟩ := FsDurReadback.fs_snap_read_ok_keep capacity.crash.disk capacity.crash.links
    capacity.crash.tops g gl gt _ state (Recovery.recovery_disk_full physical (Recovery.recover (blocks physical) covered start) covered start rfl) $$ H
  iexists g, gl, gt, state
  unfold snapshot FsBootRecovery.recovered
  iframe H
  ipureintro; exact ok

theorem prepared_of_snapshot physical covered start state
    (startTwo : start = 2) (logCovered : SnapshotHome.logRegion start ⊆ covered)
    (header : Recovery.HeaderWF (blocks physical) covered start)
    (ok : Snapshot.OK state (Recovery.recover (blocks physical) covered start)) :
    Prepared physical covered start state := by
  have facts := FsBootRecovery.recovery_facts physical covered start header
  have sb := ok.1.superblockOK
  have same : state.superblock.logstart = start := sb.logstart.trans startTwo.symm
  have ni := sb.ninodes
  have nonneg : 0 ≤ state.superblock.ninodes / 16 := Int.ediv_nonneg (by omega) (by omega)
  have weq : (width state : Int) = state.superblock.ninodes / 16 + 1 := by
    unfold width
    exact Int.toNat_of_nonneg (by omega)
  have encoded : Snapshot.OK state (SnapshotHome.restrict
      (FsBootRecovery.committed physical covered start)
      (SnapshotHome.homeSet covered state.superblock.logstart)) := by
    rw [same, facts.restricted]
    exact ok
  refine ⟨header, facts, ok, same, weq, ?_, ?_, encoded, ?_, ?_, ?_⟩
  · omega
  · have bound := sb.ushort; omega
  · rw [same]
    exact FsBootRecovery.exceptions_home physical covered start header
  · exact Recovery.writeSet_superblock _ _ _ header
  · intro b range
    apply SnapshotCoverage.snap_cov_window state (FsBootRecovery.committed physical covered start)
      covered b encoded.1
    · intro block member
      exact logCovered block (by simpa only [same] using member)
    · exact range

theorem prepare g gl gt physical covered start state
    (startTwo : start = 2) (logCovered : SnapshotHome.logRegion start ⊆ covered)
    (header : Recovery.HeaderWF (blocks physical) covered start) :
    snapshot capacity g gl gt physical covered start state ⊢
      ⌜Prepared physical covered start state⌝ ∗ snapshot capacity g gl gt physical covered start state := by
  unfold snapshot FsBootRecovery.recovered
  iintro H
  ihave ⟨%ok, H⟩ := FsDurReadback.fs_snap_read_ok_keep capacity.crash.disk capacity.crash.links
    capacity.crash.tops g gl gt _ state (Recovery.recovery_disk_full physical (Recovery.recover (blocks physical) covered start) covered start rfl) $$ H
  iframe H
  ipureintro
  exact prepared_of_snapshot physical covered start state startTwo logCovered header ok

theorem readSpec : ReadSpec capacity :=
  ⟨loan capacity, open_loan capacity, prepare capacity⟩

end MachCSL.Logic.FsCfgSnap
