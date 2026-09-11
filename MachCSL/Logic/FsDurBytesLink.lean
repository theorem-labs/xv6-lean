import MachCSL.Logic.FsDurBytesLedgerProofs
import MachCSL.Logic.FsTopLink

namespace MachCSL.Logic.FsDurBytes
open Iris Iris.Std Iris.BI

/-- The same Disk image camera at slot 12 in the actual extended registry. -/
def registryView (bytes links top : GName) : FsView.View FsTop.registry :=
  FsView.snapGamma FsTop.eraCapacity.disk bytes links top

theorem registry_disk_slot : FsTop.eraCapacity.disk.image.elem.τ = 12 := rfl

theorem provided_image_blocks γ gl gt blocks (full : BlocksFull blocks) :
    imageBytesFull FsTop.eraCapacity.disk γ (flatten blocks) ⊣⊢
      blockLedger (registryView γ gl gt) blocks := by
  rw [imageBytesFull_snapGamma FsTop.eraCapacity.disk γ gl gt]
  exact flatten_blocks _ blocks full

/-- No authority update or allocation occurs: the exact original authority
and every byte outside the selected submap are returned beside the selected bytes. -/
theorem provided_image_cut_with_auth γ (whole part : ByteMap)
    (submap : PartialMap.submap (M := Disk.ImageMap) part whole) (frame : IProp FsTop.registry) :
    imageBytesFull FsTop.eraCapacity.disk γ whole ∗
      (Disk.mapAuth FsTop.eraCapacity.disk γ whole ∗ frame) ⊢
        imageBytesFull FsTop.eraCapacity.disk γ part ∗
        imageBytesFull FsTop.eraCapacity.disk γ (PartialMap.difference (M := Disk.ImageMap) whole part) ∗
        Disk.mapAuth FsTop.eraCapacity.disk γ whole ∗ frame :=
  provided_image_cut FsTop.eraCapacity.disk γ whole part submap _

end MachCSL.Logic.FsDurBytes
