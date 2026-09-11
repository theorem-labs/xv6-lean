import MachCSL.Logic.FsBootBytesDefs

namespace MachCSL.Logic.FsBootBytes
open Iris Iris.Std Iris.BI MachCSL.Memory

structure PureSpec : Prop where
  lookup : ∀ disk covered b bytes,
    (rawMap disk covered)[b]? = some bytes ↔ b ∈ covered ∧ bytes = Xv6.Fs.blocks disk b
  domain : ∀ disk covered, FiniteMap.dom_set (M := Disk.ImageMap) (S := BlockSet) (rawMap disk covered) = covered
  full : ∀ disk covered, FsDurBytes.BlocksFull (rawMap disk covered)
  filter_in : ∀ disk covered home, home ⊆ covered →
    FsBytesBootstrap.homeMap (rawMap disk covered) home = rawMap disk home
  filter_out : ∀ disk covered home,
    FsBytesBootstrap.outsideMap (rawMap disk covered) home = rawMap disk (covered \ home)
  contained : ∀ disk length covered, Xv6.Fs.CovIn covered length →
    PartialMap.submap (M := Disk.ImageMap) (FsDurBytes.flatten (rawMap disk covered)) (suppliedMap disk length)

structure CarveSpec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  map_to_set : ∀ (predicate : Int → List Byte → IProp GF) disk covered,
    bigSepM (M := Disk.ImageMap) predicate (rawMap disk covered) ⊣⊢
      bigSepS (fun b => predicate b (Xv6.Fs.blocks disk b)) covered
  carve : ∀ diskNames disk length covered, Xv6.Fs.CovIn covered length →
    ∀ frame : IProp GF,
    DiskClient.diskBytes capacity.bytes diskNames 0 (Devices.Virtio.disk_read disk 0 length) ∗ frame ⊢
      physicalBlocks capacity diskNames disk covered ∗ remainder capacity diskNames disk length covered ∗ frame
  source_carve : ∀ diskNames disk length covered, Xv6.Fs.CovIn covered length →
    DiskClient.diskBytes capacity.bytes diskNames 0 (Devices.Virtio.disk_read disk 0 length) ⊢
      physicalBlocks capacity diskNames disk covered

structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  fs_boot_ghosts : ∀ diskNames disk length covered home device link top values exceptions,
    Xv6.Fs.CovIn covered length → home ⊆ covered →
    (∀ b, b ∈ home → (values b).length = 1024) → exceptions ⊆ home →
    (∀ b, b ∈ home → b ∉ exceptions → values b = Xv6.Fs.blocks disk b) →
    ∀ (E : CoPset) (frame : IProp GF),
    iprop(⊢ DiskClient.diskBytes capacity.bytes diskNames 0 (Devices.Virtio.disk_read disk 0 length) -∗
      frame ={E}=∗ ∃ names : Names,
      allocated capacity diskNames disk covered home device link top names values exceptions ∗
      remainder capacity diskNames disk length covered ∗ frame)

end MachCSL.Logic.FsBootBytes
