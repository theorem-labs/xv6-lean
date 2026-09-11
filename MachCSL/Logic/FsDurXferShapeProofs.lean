import MachCSL.Logic.FsDurXferShapePoolProofs
import MachCSL.Logic.FsStateProofs
import Xv6.Fs.BitmapEncodingProofs

namespace MachCSL.Logic.FsDurXferShape
open Iris Iris.Std Iris.BI Xv6.Fs DurableNode DurableState FsDurXferRuns
variable {GF : BundledGFunctors} (view : FsView.View GF)

theorem footprint_full state : FsState.footprint view (.own 1) state =
    iprop(FsView.blockOwned view 1 state.superblockBytes ∗
      bigSepM (M := FsState.InodeMap) (fun i node => FsState.inodePhi view state.superblock i node) state.inodes ∗
      FsView.blockOwned view state.superblock.bmapstart (BitmapEncoding.bitmapBytes 1024 state.used) ∗
      FsState.freePool view state.superblock.size state.used) := rfl

theorem fs_footprint_runs state : FsState.footprint view (.own 1) state ⊢
    ∃ pool, ⌜Shape state pool⌝ ∗ phiRuns view (fsRuns state pool) := by
  rw [footprint_full]
  iintro ⟨Hs, Hin, Hb, Hp⟩
  ihave ⟨%lengths, Hin⟩ := fs_inodes_phi_runs view state.superblock state.inodes $$ Hin
  ihave ⟨%pool, %pm, Hp⟩ := free_pool_runs view state.superblock.size state.used $$ Hp
  ihave %sbLength := FsView.blockOwned_length view 1 state.superblockBytes $$ Hs
  iexists pool
  isplit
  · ipureintro; exact ⟨sbLength, lengths, pm⟩
  · unfold fsRuns
    rw [(phi_runs_cons_range view _ _).to_eq, (phi_runs_cons_range view _ _).to_eq, (phi_runs_app view _ _).to_eq]
    simp only [runBlock, runOffset, runBytes]
    unfold FsView.blockOwned
    icases Hs with ⟨_, Hs⟩
    icases Hb with ⟨_, Hb⟩
    iframe Hs Hb Hin Hp

theorem fs_footprint_of_runs state pool (shape : Shape state pool) :
    phiRuns view (fsRuns state pool) ⊢ FsState.footprint view (.own 1) state := by
  unfold fsRuns
  rw [(phi_runs_cons_range view _ _).to_eq, (phi_runs_cons_range view _ _).to_eq, (phi_runs_app view _ _).to_eq]
  simp only [runBlock, runOffset, runBytes]
  iintro ⟨Hs, Hb, Hin, Hp⟩
  rw [footprint_full]
  ihave Hin := fs_inodes_phi_of_runs view state.superblock state.inodes shape.nodes $$ Hin
  ihave Hp := free_pool_of_runs view state.superblock.size state.used pool shape.pool $$ Hp
  iframe Hin Hp
  unfold FsView.blockOwned
  isplitl [Hs]
  · iframe Hs; ipureintro; exact shape.superblock
  · iframe Hb; ipureintro; exact BitmapEncoding.bitmapBytes_length 1024 state.used

theorem fs_footprint_runs_q dq state : FsState.footprint view dq state ⊢
    ∃ pool, ⌜Shape state pool⌝ ∗ phiRunsQ view (atShare dq (fsRuns state pool)) := by
  rw [FsState.footprint_gammaQ]
  iintro H
  ihave ⟨%pool, %shape, H⟩ := fs_footprint_runs (FsView.gammaQ view dq) state $$ H
  iexists pool
  isplit
  · ipureintro; exact shape
  · rw [(phi_runs_q_at view dq _).to_eq]
    iexact H

theorem fs_footprint_of_runs_q dq state pool (shape : Shape state pool) :
    phiRunsQ view (atShare dq (fsRuns state pool)) ⊢ FsState.footprint view dq state := by
  rw [(phi_runs_q_at view dq _).to_eq, FsState.footprint_gammaQ]
  exact fs_footprint_of_runs (FsView.gammaQ view dq) state pool shape

theorem shapeSpec : ShapeSpec view where
  inodeRuns := inode_phi_runs view
  inodeOfRuns := inode_phi_of_runs view
  poolRuns := free_pool_runs view
  poolOfRuns := free_pool_of_runs view
  footprintRuns := fs_footprint_runs view
  footprintOfRuns := fs_footprint_of_runs view
  fractionalRuns := fs_footprint_runs_q view
  fractionalOfRuns := fs_footprint_of_runs_q view

/-- Negative signed pool sizes retain the empty source sequence. -/
theorem negative_pool_domain nb used pool (negative : nb ≤ 0)
    (pm : PoolPM (FsState.poolIndices nb) used pool) : pool = ∅ := by
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro b
  have domain := pm.domain b
  rw [FsState.poolIndices_negative nb negative] at domain
  have absent : ¬ (pool[b]?).isSome := by simpa using domain.mp
  simpa using (Option.not_isSome_iff_eq_none.mp absent)

end MachCSL.Logic.FsDurXferShape
