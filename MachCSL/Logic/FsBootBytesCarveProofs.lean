import MachCSL.Logic.FsBootBytesPureProofs
import MachCSL.Logic.FsBytesBootstrapGrowProofs

set_option maxRecDepth 2048

namespace MachCSL.Logic.FsBootBytes
open Iris Iris.Std Iris.BI MachCSL.Memory
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem diskBlock_eq (names : DiskClient.Names) b bytes :
    DiskClient.diskBlock capacity.bytes names b bytes = FsBlocks.block capacity.bytes names.img b bytes := by
  simp only [DiskClient.diskBlock, DiskClient.diskBytes, Disk.imageBytes, Disk.imageByte,
    FsBlocks.block, FsBlocks.blockQ, FsBlocks.byteRangeQ, FsBlocks.byteElem, Int.add_zero]

theorem supplied_ledger (names : DiskClient.Names) disk length :
    DiskClient.diskBytes capacity.bytes names 0 (Devices.Virtio.disk_read disk 0 length) ⊣⊢
      FsDurBytes.imageBytesFull capacity.bytes names.img (suppliedMap disk length) :=
  (FsDurBytes.byteRun_ledger (FsView.snapGamma capacity.bytes names.img 1 1)
    0 (Devices.Virtio.disk_read disk 0 length)).symm

theorem map_to_set (predicate : Int → List Byte → IProp GF) disk covered :
    bigSepM (M := Disk.ImageMap) predicate (rawMap disk covered) ⊣⊢
      bigSepS (fun b => predicate b (Xv6.Fs.blocks disk b)) covered := by
  have pointwise : bigSepM (M := Disk.ImageMap) predicate (rawMap disk covered) =
      bigSepM (M := Disk.ImageMap) (fun b _ => predicate b (Xv6.Fs.blocks disk b)) (rawMap disk covered) := by
    apply BigSepM.bigSepM_eq
    intro b bytes found
    obtain ⟨_, rfl⟩ := (rawMap_lookup disk covered b bytes).mp found
    rfl
  rw [pointwise, (BigSepM.bigSepM_dom (S := BlockSet)).to_eq, rawMap_domain]
  exact .rfl

theorem block_ledger (names : DiskClient.Names) disk covered :
    FsDurBytes.imageBytesFull capacity.bytes names.img (FsDurBytes.flatten (rawMap disk covered)) ⊣⊢
      physicalBlocks capacity names disk covered := by
  rw [(FsBytesBootstrap.blockRuns_flatten capacity names.img _ (rawMap_full disk covered)).to_eq]
  unfold FsBytesBootstrap.blockRuns physicalBlocks
  have same : DiskClient.diskBlock capacity.bytes names = FsBlocks.block capacity.bytes names.img :=
    funext fun b => funext fun bytes => diskBlock_eq capacity names b bytes
  rw [same]
  exact map_to_set _ disk covered

theorem carve names disk length covered (bound : Xv6.Fs.CovIn covered length) (frame : IProp GF) :
    DiskClient.diskBytes capacity.bytes names 0 (Devices.Virtio.disk_read disk 0 length) ∗ frame ⊢
      physicalBlocks capacity names disk covered ∗ remainder capacity names disk length covered ∗ frame := by
  rw [(supplied_ledger capacity names disk length).to_eq]
  iintro H
  ihave ⟨Hblocks, Hrest, Hframe⟩ := FsDurBytes.provided_image_cut capacity.bytes names.img
    (suppliedMap disk length) (FsDurBytes.flatten (rawMap disk covered))
    (covered_bytes_submap disk length covered bound) frame $$ H
  ihave Hb := (block_ledger capacity names disk covered).mp $$ Hblocks
  unfold remainder remainderMap
  iframe Hb Hrest Hframe

theorem source_carve names disk length covered (bound : Xv6.Fs.CovIn covered length) :
    DiskClient.diskBytes capacity.bytes names 0 (Devices.Virtio.disk_read disk 0 length) ⊢
      physicalBlocks capacity names disk covered := by
  iintro H
  ihave ⟨Hb, _, _⟩ := carve capacity names disk length covered bound emp $$ [$H]
  iexact Hb

theorem carveSpec : CarveSpec capacity := ⟨map_to_set, carve capacity, source_carve capacity⟩

end MachCSL.Logic.FsBootBytes
