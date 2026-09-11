import MachCSL.Logic.FsDurReadbackSpec
import MachCSL.Logic.FsDurCouplingMetadataProofs
import MachCSL.Logic.FsDurInodeReadProofs
import MachCSL.Logic.FsDurSnapshotProofs
import MachCSL.Logic.FsStateLinkGatherProofs

namespace MachCSL.Logic.FsDurReadback
open Iris Iris.Std Iris.BI Xv6.Fs DurableState DurableNode
variable {GF : BundledGFunctors}

/-- Source FsState.fs_geom_inum, derived from the rounded region bound. -/
theorem geometry_inum (state : State) (geometry : Geometry state) (i : Int) node
    (found : state.inodes[i]? = some node) : 0 ≤ i ∧ i < 2 ^ 32 := by
  have region := geometry.region i node found
  have bmap := geometry.superblock.bmapstart
  have upper := geometry.superblock.ushort
  omega

/-- The padded inode region contains every advertised inode index. -/
theorem geometry_domain (state : State) (geometry : Geometry state) i
    (bound : 0 ≤ i ∧ i < state.superblock.ninodes) : (state.inodes[i]?).isSome := by
  apply geometry.domain
  omega

theorem pureState_local (state : State) : FsState.pureState (GF := GF) state ⊢ ⌜DurableState.Local state⌝ := by
  unfold FsState.pureState DurableState.Local
  iintro ⟨_, Hl, _⟩
  iapply pure_forall.mpr
  iintro %i
  iapply pure_forall.mpr
  iintro %node
  iapply pure_imp.mpr
  iintro %found
  iapply BigSepM.bigSepM_lookup (M := FsState.InodeMap) found $$ Hl

theorem footprint_one (view : FsView.View GF) state : FsState.footprint view (.own 1) state =
    iprop(FsView.blockOwned view 1 state.superblockBytes ∗
      FsDurInodeRead.inodeLeg view state.superblock state.inodes ∗
      FsView.blockOwned view state.superblock.bmapstart (BitmapEncoding.bitmapBytes 1024 state.used) ∗
      FsState.freePool view state.superblock.size state.used) := rfl

variable (dc : Disk.Capacity GF) (lc : FsLink.Capacity GF) (tc : FsTop.Capacity GF)

theorem fs_snap_read_ok g gl gt disk state (full : FsDurBytes.BlocksFull disk) :
    FsDurSnapshot.fsSnap dc lc tc (FsView.snapGamma dc g gl gt) g disk state ⊢ ⌜Snapshot.OK state disk⌝ := by
  unfold FsDurSnapshot.fsSnap
  iintro ⟨Ha, _, _, Hstate, Hroot, %shape⟩
  ihave ⟨Hfoot, Hghost⟩ := (FsState.state_split (FsView.snapGamma dc g gl gt) lc (.own 1) state).mp $$ Hstate
  ihave ⟨Hlinks, Hpure⟩ := (FsState.ghost_split (FsView.snapGamma dc g gl gt) lc state).mp $$ Hghost
  ihave %locals := pureState_local state $$ Hpure
  unfold FsState.pureState
  icases Hpure with ⟨%parse, _, %geometry⟩
  have bounds := geometry_inum state geometry
  rw [footprint_one]
  icases Hfoot with ⟨Hs, Hin, Hb, Hp⟩
  ihave %superblock := FsDurRead.snap_blk_read_full dc g gl gt disk 1 state.superblockBytes full $$ [$Ha $Hs]
  ihave %bitmap := FsDurRead.snap_blk_read_full dc g gl gt disk state.superblock.bmapstart
    (BitmapEncoding.bitmapBytes 1024 state.used) full $$ [$Ha $Hb]
  ihave %nodes := FsDurInodeRead.snap_read_inodes dc g gl gt disk state.superblock state.inodes full bounds locals $$ [$Ha $Hin]
  ihave %pool := FsDurInodeRead.snap_read_pool dc g gl gt disk state.superblock.size state.used full $$ [$Ha $Hp]
  have exclusive := FsView.snapGamma_excl dc g gl gt
  ihave %disjoint := FsDurCoupling.fs_inodes_phi_disj (FsView.snapGamma dc g gl gt) exclusive state.superblock state.inodes $$ Hin
  ihave %used := FsDurCoupling.fs_inodes_phi_used (FsView.snapGamma dc g gl gt) exclusive state.superblock state.inodes
    state.superblock.size state.used $$ [$Hp $Hin]
  have notMeta := FsDurCoupling.fs_owns_not_meta (FsView.snapGamma dc g gl gt) exclusive state bounds locals
  have metaUsed := FsDurCoupling.fs_meta_used (FsView.snapGamma dc g gl gt) exclusive state bounds locals
  unfold FsDurCoupling.metadataLeg at notMeta metaUsed
  ihave %notMetadata := notMeta $$ [$Hs $Hb $Hin]
  ihave %metadataUsed := metaUsed $$ [$Hs $Hb $Hin $Hp]
  icases Hroot with ⟨%ty, Hroot⟩
  ihave %links := FsState.links_valid_tok lc (FsView.snapGamma dc g gl gt).link state.inodes 1 ty $$ Hlinks Hroot
  ipureintro
  refine ⟨?_, locals⟩
  refine {
    blockSize := full
    superblock := superblock
    parse := parse
    bitmap := bitmap
    pool := pool
    inum := bounds
    repr := fun i node found => DurableNode.repr_of_local (locals i node found)
    record := fun i node found => (nodes i node found).record
    data := fun i node k bytes found get => (nodes i node found).data k bytes get
    indirect := fun i node found => (nodes i node found).indirect
    domain := geometry_domain state geometry
    links := ?_
    metadataUsed := ?_
    ownedUsed := ?_
    disjoint := disjoint
    superblockOK := geometry.superblock
    region := geometry.region
    slot := fun i node found => (nodes i node found).slot
    regionDomain := geometry.domain
    directory := geometry.directory
    domainBelow := shape.domainBelow }
  · obtain ⟨f, ok, valid⟩ := links
    exact ⟨f, ty, ok, valid⟩
  · intro b isMetadata
    apply metadataUsed b isMetadata
    apply shape.domainBelow
    rcases isMetadata with rfl | rfl | ⟨i, present, rfl⟩
    · simp [superblock]
    · simp [bitmap]
    · obtain ⟨node, found⟩ := Option.isSome_iff_exists.mp present
      obtain ⟨bytes, get, _⟩ := (nodes i node found).record
      simp [get]
  · intro i node b found owns
    refine ⟨used i node b found owns ?_, notMetadata i node b found owns⟩
    apply shape.domainBelow
    rcases owns with ⟨k, present, rfl⟩ | ⟨nonzero, rfl⟩
    · obtain ⟨bytes, get⟩ := Option.isSome_iff_exists.mp present
      simp [(nodes i node found).data k bytes get]
    · simp [(nodes i node found).indirect nonzero]

theorem fs_snap_read_ok_keep g gl gt disk state (full : FsDurBytes.BlocksFull disk) :
    FsDurSnapshot.fsSnap dc lc tc (FsView.snapGamma dc g gl gt) g disk state ⊢
      ⌜Snapshot.OK state disk⌝ ∗ FsDurSnapshot.fsSnap dc lc tc (FsView.snapGamma dc g gl gt) g disk state := by
  iintro H
  ihave %ok := fs_snap_read_ok dc lc tc g gl gt disk state full $$ H
  iframe H
  ipureintro
  exact ok

theorem P_dur_tie disk (full : FsDurBytes.BlocksFull disk) :
    FsDurSnapshot.Pdur dc lc tc disk ⊢ ∃ state, ⌜Snapshot.OK state disk⌝ := by
  unfold FsDurSnapshot.Pdur
  iintro ⟨%g, %gl, %gt, %state, H⟩
  iexists state
  iapply fs_snap_read_ok dc lc tc g gl gt disk state full $$ H

theorem P_dur_tie_keep disk (full : FsDurBytes.BlocksFull disk) :
    FsDurSnapshot.Pdur dc lc tc disk ⊢ ∃ state, ⌜Snapshot.OK state disk⌝ ∗ FsDurSnapshot.Pdur dc lc tc disk := by
  iintro H
  ihave ⟨%state, %ok⟩ := P_dur_tie dc lc tc disk full $$ H
  iexists state
  iframe H
  ipureintro
  exact ok

theorem readbackSpec : ReadbackSpec dc lc tc where
  snapshot := fs_snap_read_ok dc lc tc
  snapshotKeep := fs_snap_read_ok_keep dc lc tc
  durable := P_dur_tie dc lc tc
  durableKeep := P_dur_tie_keep dc lc tc

end MachCSL.Logic.FsDurReadback
