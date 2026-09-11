import MachCSL.Logic.FsDurXferShapeSpec
import MachCSL.Logic.FsDurXferRunsProofs
import MachCSL.Logic.FsStateInodeProofs

namespace MachCSL.Logic.FsDurXferShape
open Iris Iris.Std Iris.BI Xv6.Fs DurableNode DurableState FsDurXferRuns
variable {GF : BundledGFunctors} (view : FsView.View GF)

theorem rec_owned_run sb i node : FsState.recOwned view sb i node.record ⊣⊢ phiRuns view [recordRun sb i node] := by
  unfold phiRuns
  rw [BigSepL.bigSepL_singleton.to_eq]
  exact .rfl

theorem inode_data_lengths node : FsState.inodeDat view node ⊢ ⌜NodeLens node⌝ := by
  unfold FsState.inodeDat FsState.inodeDatQ
  iintro ⟨Hd, Hi⟩
  have both : (NodeLens node) ↔
      (∀ (k : Nat) bytes, node.blocks[k]? = some bytes → bytes.length = 1024) ∧
      (node.indirect ≠ 0 → (indirectBytes node.entries).length = 1024) := ⟨fun h => ⟨h.data, h.indirect⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [both]
  iapply pure_and.mp
  isplit
  · iapply pure_forall.mpr
    iintro %k
    iapply pure_forall.mpr
    iintro %bytes
    iapply pure_imp.mpr
    iintro %found
    ihave Hb := BigSepM.bigSepM_lookup (M := FsState.SlotMap) found $$ Hd
    iapply FsView.blockOwnedQ_length view (.own 1) (node.address k) bytes $$ Hb
  · iapply pure_imp.mpr
    iintro %nonzero
    unfold FsState.indOwnedQ
    rw [if_neg nonzero]
    iapply FsView.blockOwnedQ_length view (.own 1) node.indirect (indirectBytes node.entries) $$ Hi

theorem inode_dats_runs node : FsState.inodeDat view node ⊢ ⌜NodeLens node⌝ ∗ phiRuns view (dataRuns node) := by
  iintro H
  ihave %lengths := inode_data_lengths view node $$ H
  isplit
  · ipureintro; exact lengths
  · unfold FsState.inodeDat FsState.inodeDatQ
    icases H with ⟨Hd, Hi⟩
    unfold dataRuns
    rw [(phi_runs_app view _ _).to_eq]
    isplitl [Hd]
    · unfold phiRuns
      rw [BigSepL.bigSepL_map]
      have use : (bigSepM (M := FsState.SlotMap) (fun k bytes => FsView.blockOwnedQ view (.own 1) (node.address k) bytes) node.blocks) ⊢
          bigSepL (fun _ entry => FsView.byteRange view (runBlock (dataRun node entry)) (runOffset (dataRun node entry)) (runBytes (dataRun node entry)))
            (FiniteMap.toList (M := FsState.SlotMap) node.blocks) := by
        rw [BigSepM.bigSepM_toList.to_eq]
        apply BigSepL.bigSepL_mono_of_forall
        intro k entry
        unfold FsView.blockOwnedQ
        iintro ⟨_, Hb⟩
        simp only [runBlock, runOffset, runBytes, dataRun, FsView.byteRange]
        iexact Hb
      iapply use $$ Hd
    · unfold indirectRuns FsState.indOwnedQ
      split
      · rw [(phi_runs_nil view).to_eq]; iexact Hi
      · unfold phiRuns
        rw [BigSepL.bigSepL_singleton.to_eq]
        unfold FsView.blockOwnedQ
        icases Hi with ⟨_, Hb⟩
        simp only [runBlock, runOffset, runBytes, FsView.byteRange]
        iexact Hb

theorem inode_dats_of_runs node (lengths : NodeLens node) :
    phiRuns view (dataRuns node) ⊢ FsState.inodeDat view node := by
  unfold dataRuns FsState.inodeDat FsState.inodeDatQ
  rw [(phi_runs_app view _ _).to_eq]
  iintro ⟨Hd, Hi⟩
  isplitl [Hd]
  · unfold phiRuns
    rw [BigSepL.bigSepL_map]
    have use : bigSepL (fun _ entry => FsView.byteRange view (runBlock (dataRun node entry)) (runOffset (dataRun node entry)) (runBytes (dataRun node entry)))
        (FiniteMap.toList (M := FsState.SlotMap) node.blocks) ⊢
        bigSepM (M := FsState.SlotMap) (fun k bytes => FsView.blockOwnedQ view (.own 1) (node.address k) bytes) node.blocks := by
      rw [BigSepM.bigSepM_toList.to_eq]
      apply BigSepL.bigSepL_mono
      intro k entry found
      have get := (LawfulFiniteMap.toList_get (M := FsState.SlotMap) (m := node.blocks) (k := entry.1) (v := entry.2)).mp (List.mem_of_getElem? found)
      unfold FsView.blockOwnedQ
      iintro Hb
      isplit
      · ipureintro; exact lengths.data entry.1 entry.2 get
      · simp only [runBlock, runOffset, runBytes, dataRun, FsView.byteRange]; iexact Hb
    iapply use $$ Hd
  · unfold indirectRuns FsState.indOwnedQ
    split
    · rw [(phi_runs_nil view).to_eq]; iexact Hi
    · rename_i nonzero
      unfold phiRuns
      rw [BigSepL.bigSepL_singleton.to_eq]
      unfold FsView.blockOwnedQ
      isplit
      · ipureintro; exact lengths.indirect nonzero
      · simp only [runBlock, runOffset, runBytes, FsView.byteRange]; iexact Hi

theorem inode_phi_runs sb i node : FsState.inodePhi view sb i node ⊢ ⌜NodeLens node⌝ ∗ phiRuns view (inodeRuns sb i node) := by
  unfold FsState.inodePhi inodeRuns
  rw [(phi_runs_cons_range view _ _).to_eq]
  iintro ⟨Hr, Hd⟩
  ihave ⟨%lengths, Hd⟩ := inode_dats_runs view node $$ Hd
  iframe Hd
  isplit
  · ipureintro; exact lengths
  · have eq : FsState.recOwned view sb i node.record = FsView.byteRange view (runBlock (recordRun sb i node)) (runOffset (recordRun sb i node)) (runBytes (recordRun sb i node)) := rfl
    rw [← eq]
    iexact Hr

theorem inode_phi_of_runs sb i node (lengths : NodeLens node) : phiRuns view (inodeRuns sb i node) ⊢ FsState.inodePhi view sb i node := by
  unfold inodeRuns FsState.inodePhi
  rw [(phi_runs_cons_range view _ _).to_eq]
  iintro ⟨Hr, Hd⟩
  ihave Hd := inode_dats_of_runs view node lengths $$ Hd
  iframe Hd
  have eq : FsState.recOwned view sb i node.record = FsView.byteRange view (runBlock (recordRun sb i node)) (runOffset (recordRun sb i node)) (runBytes (recordRun sb i node)) := rfl
  rw [eq]
  iexact Hr

theorem phi_runs_concat lists : phiRuns view lists.flatten ⊣⊢ bigSepL (fun _ runs => phiRuns view runs) lists := by
  induction lists with
  | nil => exact .rfl
  | cons runs lists ih =>
    simp only [List.flatten_cons]
    rw [(phi_runs_app view _ _).to_eq, ih.to_eq]
    exact .rfl

theorem fs_inodes_phi_runs sb nodes :
    bigSepM (M := FsState.InodeMap) (fun i node => FsState.inodePhi view sb i node) nodes ⊢
      ⌜∀ (i : Int) node, nodes[i]? = some node → NodeLens node⌝ ∗ phiRuns view (inodesRuns sb nodes) := by
  iintro H
  isplit
  · iapply pure_forall.mpr
    iintro %i
    iapply pure_forall.mpr
    iintro %node
    iapply pure_imp.mpr
    iintro %found
    ihave Hnode := BigSepM.bigSepM_lookup (M := FsState.InodeMap) found $$ H
    ihave ⟨Hlen, _⟩ := inode_phi_runs view sb i node $$ Hnode
    iexact Hlen
  · unfold inodesRuns phiRuns
    rw [BigSepL.bigSepL_flatMap, BigSepM.bigSepM_toList.to_eq]
    iapply BigSepL.bigSepL_mono_of_forall (fun {k entry} => ?_) $$ H
    iintro Hnode
    ihave ⟨_, Hr⟩ := inode_phi_runs view sb entry.1 entry.2 $$ Hnode
    unfold phiRuns
    iexact Hr

theorem fs_inodes_phi_of_runs sb nodes
    (lengths : ∀ (i : Int) node, nodes[i]? = some node → NodeLens node) :
    phiRuns view (inodesRuns sb nodes) ⊢ bigSepM (M := FsState.InodeMap) (fun i node => FsState.inodePhi view sb i node) nodes := by
  unfold inodesRuns phiRuns
  rw [BigSepL.bigSepL_flatMap, BigSepM.bigSepM_toList.to_eq]
  apply BigSepL.bigSepL_mono
  intro k entry found
  have get := (LawfulFiniteMap.toList_get (M := FsState.InodeMap) (m := nodes) (k := entry.1) (v := entry.2)).mp (List.mem_of_getElem? found)
  exact inode_phi_of_runs view sb entry.1 entry.2 (lengths entry.1 entry.2 get)

end MachCSL.Logic.FsDurXferShape
