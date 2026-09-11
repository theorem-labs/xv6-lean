import MachCSL.Logic.FsDurAssembleGroupProofs
import MachCSL.Logic.FsStateLinkProofs

namespace MachCSL.Logic.FsDurAssemble
open Iris Iris.Std Iris.BI Xv6.Fs DurableState DurableNode FsView FsDurAlloc FsDurBytes
variable {GF : BundledGFunctors} (view : View GF)

theorem slots_to_footprint (state : State) disk (bytes : Snapshot.Bytes state disk) :
    slotLedger view state disk ⊢ FsState.footprint view (.own 1) state := by
  iintro Hslots
  ihave ⟨Hsb, Hbmap, ⟨⟨⟨Hrec, Hdata⟩, Hind⟩, Hpool⟩⟩ := (slots_grouped view state disk).mp $$ Hslots
  ihave Hrec := record_slots view state disk bytes $$ Hrec
  ihave Hdata := data_slots view state disk bytes $$ Hdata
  ihave Hind := indirect_slots view state disk bytes $$ Hind
  ihave Hpool := pool_slots view state disk bytes $$ Hpool
  have inodeJoin :
      (bigSepM (M := FsState.InodeMap) (fun i n => FsState.recOwned view state.superblock i n.record) state.inodes ∗
        bigSepM (M := FsState.InodeMap) (fun _ n => bigSepM (M := FsState.SlotMap)
          (fun k block => blockOwned view (n.address k) block) n.blocks) state.inodes) ∗
        bigSepM (M := FsState.InodeMap) (fun _ n => FsState.indOwned view n) state.inodes ⊢
      bigSepM (M := FsState.InodeMap) (fun i n => FsState.inodePhi view state.superblock i n) state.inodes := by
    rw [← BigSepM.bigSepM_sep_eq, ← BigSepM.bigSepM_sep_eq]
    apply BigSepM.bigSepM_mono
    intro i n _
    unfold FsState.inodePhi FsState.inodeDat FsState.inodeDatQ
    exact sep_assoc.mp
  ihave Hinodes := inodeJoin $$ [$Hrec $Hdata $Hind]
  unfold FsState.footprint
  rw [gammaQ_one_blockOwned, gammaQ_one_blockOwned]
  rw [show (fun i n => FsState.inodePhi (gammaQ view (.own 1)) state.superblock i n) =
    (fun i n => FsState.inodePhi view state.superblock i n) from rfl]
  rw [show FsState.freePool (gammaQ view (.own 1)) state.superblock.size state.used =
    FsState.freePool view state.superblock.size state.used from rfl]
  isplitl [Hsb]
  · unfold blockOwned
    isplit
    · ipureintro; exact bytes.blockSize 1 _ bytes.superblock
    · iexact Hsb
  isplitl [Hinodes]
  · iexact Hinodes
  isplitl [Hbmap]
  · unfold blockOwned
    isplit
    · ipureintro; exact bytes.blockSize _ _ bytes.bitmap
    · iexact Hbmap
  · iexact Hpool

theorem pureState_intro (state : State) disk (ok : Snapshot.OK state disk) : ⊢ FsState.pureState (GF := GF) state := by
  unfold FsState.pureState
  isplit
  · ipureintro; exact ok.1.parse
  isplit
  · iapply BigSepM.bigSepM_pure.mpr
    ipureintro
    intro i n found
    exact ok.2 i n found
  · ipureintro; exact Snapshot.bytes_geometry ok.1

variable (capacity : FsLink.Capacity GF)

theorem state_of_slots (state : State) disk (ok : Snapshot.OK state disk) :
    slotLedger view state disk ∗ FsState.links capacity view.link state.inodes ⊢
      FsState.state view capacity (.own 1) state := by
  iintro ⟨Hslots, Hlinks⟩
  ihave Hfoot := slots_to_footprint view state disk ok.1 $$ Hslots
  iapply (FsState.state_split view capacity (.own 1) state).mpr
  iframe Hfoot
  iapply (FsState.ghost_split view capacity state).mpr
  iframe Hlinks
  iapply pureState_intro state disk ok

theorem slots_maps (state : State) disk :
    bigSepL (fun _ x => byteLedger view (fpMap state disk x)) (family state) ⊣⊢ slotLedger view state disk := by
  unfold slotLedger
  constructor
  · exact BigSepL.bigSepL_mono (fun _ => (byteRange_run view _ _ _).mpr)
  · exact BigSepL.bigSepL_mono (fun _ => (byteRange_run view _ _ _).mp)

theorem state_of_image (state : State) disk (ok : Snapshot.OK state disk) (whole : ByteMap)
    (coverage : PartialMap.submap (M := Disk.ImageMap) (flatten disk) whole) (frame : IProp GF) :
    byteLedger view whole ∗ FsState.links capacity view.link state.inodes ∗ frame ⊢
      FsState.state view capacity (.own 1) state ∗ remainder view whole state disk ∗ frame := by
  have cut := ledger_carve view whole (family state) (fpMap state disk)
    (family_nodup state)
    (fun x mem => PartialMap.subset_trans
      (fp_ok state disk x ok.1 ((family_mem state x).mp mem)).1 coverage)
    (fun x y hx hy ne => fp_disjoint state disk x y ok.1
      ((family_mem state x).mp hx) ((family_mem state y).mp hy) ne)
    (iprop(FsState.links capacity view.link state.inodes ∗ frame))
  rw [(slots_maps view state disk).to_eq] at cut
  iintro H
  ihave ⟨Hslots, Hrest, Hlinks, Hframe⟩ := cut $$ H
  ihave Hstate := state_of_slots view capacity state disk ok $$ [$Hslots $Hlinks]
  iframe Hstate Hframe
  unfold remainder remainderMap
  iexact Hrest

theorem state_of_blocks (state : State) disk (ok : Snapshot.OK state disk) (frame : IProp GF) :
    blockLedger view disk ∗ FsState.links capacity view.link state.inodes ∗ frame ⊢
      FsState.state view capacity (.own 1) state ∗ remainder view (flatten disk) state disk ∗ frame := by
  rw [← (flatten_blocks view disk ok.1.blockSize).to_eq]
  exact state_of_image view capacity state disk ok (flatten disk) (PartialMap.subset_refl _) frame

theorem assemblySpec : AssemblySpec view capacity where
  slots := slots_to_footprint view
  blocks := state_of_blocks view capacity
  image := state_of_image view capacity

end MachCSL.Logic.FsDurAssemble
