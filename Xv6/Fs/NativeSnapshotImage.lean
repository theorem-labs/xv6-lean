import Xv6.Fs.SnapshotImage
import MachCSL.Logic.FsDurSnapshotLink

/-! The literal initial-image caller of the source value-first constructor.
Generic native allocation and runtime transport never import this leaf. -/
namespace Xv6.Fs.Image.NativeSnapshot
open Iris Iris.Std Iris.BI MachCSL.Logic DurableImageNode SnapshotHome

abbrev state : DurableState.State := imageState blockView superblock 13
abbrev committed : DurableState.BlockMap := homeMap blockView initialCoverage superblock.logstart

attribute [local irreducible] DurableImageNode.imageState SnapshotHome.homeMap

theorem home_lookup (b : Int) : committed[b]? =
    if 1 ≤ b ∧ b < 2000 ∧ ¬(2 ≤ b ∧ b < 33) then some (blockView b) else none := by
  rw [homeMap_lookup]
  simp only [initial_coverage, and_assoc]
  rfl

/-- Each byte in the committed home map is independently tied to the same
artifact disk value used by the physical-authority theorem below. -/
theorem flattened_home_byte (address : Int) (byte : MachCSL.Memory.Byte)
    (found : (FsDurBytes.flatten committed)[address]? = some byte) : disk address = byte := by
  obtain ⟨b, bytes, k, stored, get, location⟩ :=
    (FsDurBytes.flatten_lookup committed address byte
      (FsDurBytes.dbytesOK_full committed snapshot_ok.1.blockSize)).mp found
  have source : bytes = blockView b := by
    rw [home_lookup] at stored
    split at stored
    · exact (Option.some.inj stored).symm
    · cases stored
  have inRange := (List.getElem?_eq_some_iff.mp get).1
  rw [source, blocks_length] at inRange
  have atByte : byteAt (blockView b) k = byte := by
    simp only [← source, byteAt, get, Option.getD_some]
  rw [blocks_byte disk b k inRange] at atByte
  rwa [location]

/-- Literal initial producer; retains the exact uncarved snapshot bytes. -/
theorem allocate_snapshot (frame : IProp FsTop.registry) :
    iprop(frame ⊢ |==> ∃ g gl gt,
      FsDurSnapshot.fsSnap FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity
        (FsView.snapGamma FsTop.eraCapacity.disk g gl gt) g committed state ∗
      MachCSL.Logic.FsDurAssemble.remainder (FsView.snapGamma FsTop.eraCapacity.disk g gl gt)
        (FsDurBytes.flatten committed) state committed ∗ frame) :=
  FsDurSnapshot.Initial.fs_snap_alloc FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity
    state committed snapshot_ok frame

theorem allocate_durable (frame : IProp FsTop.registry) :
    iprop(frame ⊢ |==> (FsDurSnapshot.registryPdur committed ∗ frame)) :=
  FsDurSnapshot.Initial.P_dur_alloc FsTop.eraCapacity.disk FsTop.linkCapacity FsTop.registryCapacity
    state committed snapshot_ok frame

/-- The original physical authority stands at the very same checked image
value as the pure home-byte tie above; allocation does not replace it. -/
theorem allocate_with_physical_authority (physicalName : GName) (frame : IProp FsTop.registry) :
    iprop(Disk.imageAuth FsTop.eraCapacity.disk physicalName disk ∗ frame ⊢ |==>
      (FsDurSnapshot.registryPdur committed ∗
        Disk.imageAuth FsTop.eraCapacity.disk physicalName disk ∗ frame)) :=
  FsDurSnapshot.Initial.preserve_physical_authority state committed snapshot_ok physicalName disk frame

end Xv6.Fs.Image.NativeSnapshot
