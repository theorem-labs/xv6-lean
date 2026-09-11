import MachCSL.Logic.FsDurAllocLedgerProofs
import MachCSL.Logic.FsDurBytesLink

namespace MachCSL.Logic.FsDurAlloc
open Iris Iris.Std Iris.BI Xv6.Fs DurableState FsDurBytes

/-- Carve an existing disk image ledger, keeping its original authority and
all bytes outside the complete footprint. The disk block map may cover only
a submap of the supplied image. No fresh byte ghost name is allocated. -/
theorem provided_image_carve (γ gl gt : GName) (state : State) disk
    (bytes : Snapshot.Bytes state disk) (whole : ByteMap)
    (coverage : PartialMap.submap (M := Disk.ImageMap) (flatten disk) whole)
    (frame : IProp FsTop.registry) :
    imageBytesFull FsTop.eraCapacity.disk γ whole ∗
      (Disk.mapAuth FsTop.eraCapacity.disk γ whole ∗ frame) ⊢
      slotLedger (registryView γ gl gt) state disk ∗
      imageBytesFull FsTop.eraCapacity.disk γ
        (PartialMap.difference (M := Disk.ImageMap) whole (selected (family state) (fpMap state disk))) ∗
      Disk.mapAuth FsTop.eraCapacity.disk γ whole ∗ frame := by
  let view := registryView γ gl gt
  have cut := ledger_carve view whole (family state) (fpMap state disk)
    (family_nodup state)
    (fun x mem => PartialMap.subset_trans
      (fp_ok state disk x bytes ((family_mem state x).mp mem)).1 coverage)
    (fun x y hx hy ne => fp_disjoint state disk x y bytes
      ((family_mem state x).mp hx) ((family_mem state y).mp hy) ne)
    (BIBase.sep (Disk.mapAuth FsTop.eraCapacity.disk γ whole) frame)
  have runs : bigSepL (fun _ x => byteLedger view (fpMap state disk x)) (family state) ⊣⊢
      slotLedger view state disk := by
    unfold slotLedger
    constructor
    · exact BigSepL.bigSepL_mono (fun _ => (byteRange_run view _ _ _).mpr)
    · exact BigSepL.bigSepL_mono (fun _ => (byteRange_run view _ _ _).mp)
  rw [runs.to_eq] at cut
  exact cut

theorem zero_pool_in_family state (positive : 0 < state.superblock.size) :
    Slot.pool 0 ∈ family state :=
  (family_mem state (.pool 0)).mpr ⟨by decide, positive⟩

theorem used_pool_empty state disk b (used : b ∈ state.used) :
    fpMap state disk (.pool b) = ∅ := by simp only [fpMap, fpBytes, if_pos used, fpRun_empty]

end MachCSL.Logic.FsDurAlloc
