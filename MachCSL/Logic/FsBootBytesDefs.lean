import MachCSL.Logic.BioViewDefs
import MachCSL.Logic.FsBytesBootstrapDefs
import Xv6.Fs.BootImageDefs

/-! FsBoot's raw covered map, exact buffer-pool columns and complete native
byte mint result. The physical image name is supplied, not allocated here. -/
namespace MachCSL.Logic.FsBootBytes
open Iris Iris.Std Iris.BI MachCSL.Memory

abbrev Capacity := FsBytesBootstrap.Capacity
abbrev Names := FsBlocks.Names
abbrev BlockSet := Xv6.Fs.BlockSet
abbrev BlockMap := Xv6.Fs.DurableState.BlockMap
abbrev ByteMap := FsDurBytes.ByteMap
abbrev Physical := Xv6.Fs.Disk

def rawMap (disk : Physical) (covered : BlockSet) : BlockMap :=
  Xv6.Fs.SnapshotHome.restrict (Xv6.Fs.blocks disk) covered

def dirtyMap (disk : Physical) (covered : BlockSet) : FsBlockGhost.BlockMap Bool :=
  FsBytesBootstrap.cleanMap (rawMap disk covered)

def suppliedMap (disk : Physical) (length : Nat) : ByteMap :=
  FsDurBytes.byteRun 0 (Devices.Virtio.disk_read disk 0 length)

def remainderMap (disk : Physical) (length : Nat) (covered : BlockSet) : ByteMap :=
  PartialMap.difference (M := Disk.ImageMap) (suppliedMap disk length) (FsDurBytes.flatten (rawMap disk covered))

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Every source field is retained; only clean/dirty predicates are specialized. -/
def fsView (names : Names) (diskNames : DiskClient.Names) (device : BitVec 32)
    (covered : BlockSet) : BioView.View GF where
  names := diskNames
  device := device
  covered := covered
  clean := FsBlockGhost.mclean capacity.blocks names
  dirty := FsBlockGhost.mdirty capacity.blocks names
  cleanTimeless := by
    intro b bytes
    letI := capacity.blocks.cache
    letI := capacity.blocks.dirty
    unfold FsBlockGhost.mclean FsBlockGhost.chalf FsBlockGhost.dirtyHalf
      FsBlockGhost.cacheElem FsBlockGhost.dirtyElem
    infer_instance
  dirtyTimeless := by
    intro b bytes
    letI := capacity.blocks.cache
    letI := capacity.blocks.dirty
    unfold FsBlockGhost.mdirty FsBlockGhost.chalf FsBlockGhost.dirtyHalf
      FsBlockGhost.cacheElem FsBlockGhost.dirtyElem
    infer_instance

def physicalBlocks (diskNames : DiskClient.Names) (disk : Physical) (covered : BlockSet) : IProp GF :=
  bigSepS (fun b => DiskClient.diskBlock capacity.bytes diskNames b (Xv6.Fs.blocks disk b)) covered

def remainder (diskNames : DiskClient.Names) (disk : Physical) (length : Nat)
    (covered : BlockSet) : IProp GF :=
  FsDurBytes.imageBytesFull capacity.bytes diskNames.img (remainderMap disk length covered)

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- Exact source fs_boot_ghosts result. Its physical remainder is returned
separately by the stronger framed contract; all source output columns remain. -/
def allocated (diskNames : DiskClient.Names) (disk : Physical) (covered home : BlockSet)
    (device : BitVec 32) (link top : GName) (names : Names) (values : Xv6.Fs.Blocks)
    (exceptions : BlockSet) : IProp GF :=
  iprop(⌜names.link = link⌝ ∗ ⌜names.top = top⌝ ∗
    bigSepS (BioView.poolBlock capacity.bytes (fsView capacity names diskNames device covered)) covered ∗
    FsBlockGhost.cacheAuth capacity.blocks names (rawMap disk covered) ∗
    FsBlockGhost.dirtyAuth capacity.blocks names (dirtyMap disk covered) ∗
    FsBytesInvariant.invariant capacity names home values ∗
    FsBlockGhost.exc_own capacity.blocks names.exceptions exceptions ∗
    bigSepS (fun b => FsBlockGhost.dirtyHalf capacity.blocks names b false) covered ∗
    bigSepS (fun b => FsBlocks.block capacity.bytes names.bytes b (values b)) home ∗
    bigSepS (fun b => FsBlockGhost.chalf capacity.blocks names b (Xv6.Fs.blocks disk b)) (covered \ home))

end MachCSL.Logic.FsBootBytes
