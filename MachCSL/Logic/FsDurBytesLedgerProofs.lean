import MachCSL.Logic.FsDurBytesProofs
import MachCSL.Logic.FsViewLink

namespace MachCSL.Logic.FsDurBytes
open Iris Iris.Std Iris.BI MachCSL.Memory
variable {GF : BundledGFunctors} (view : FsView.View GF)

theorem byteRun_ledger start bytes : byteLedger view (byteRun start bytes) ⊣⊢ FsView.byteRange view 0 start bytes := by
  have law := BigSepM.bigSepM_map_seqZ (M' := Disk.ImageMap)
    (Φ := fun a v => view.phi (.own 1) a v) (start := start) (l := bytes)
  simpa only [byteLedger, byteRun, FsView.byteRange, FsView.byteRangeQ, Int.zero_mul, Int.zero_add] using law

theorem byteRange_run (b off : Int) bytes :
    FsView.byteRange view b off bytes ⊣⊢ byteLedger view (byteRun (b * 1024 + off) bytes) := by
  have law := (byteRun_ledger view (b * 1024 + off) bytes).symm
  simpa only [FsView.byteRange, FsView.byteRangeQ, Int.zero_mul, Int.zero_add] using law

theorem blockOwned_run b bytes (full : bytes.length = 1024) :
    FsView.blockOwned view b bytes ⊣⊢ byteLedger view (byteRun (b * 1024) bytes) := by
  unfold FsView.blockOwned
  rw [(byteRange_run view b 0 bytes).to_eq, Int.add_zero]
  constructor
  · iintro ⟨_, H⟩; iexact H
  · iintro H; iframe H; ipureintro; exact full

theorem byteLedger_union (left right : ByteMap)
    (disjoint : PartialMap.disjoint (M := Disk.ImageMap) left right) :
    byteLedger view (leftUnion left right) ⊣⊢ byteLedger view left ∗ byteLedger view right :=
  BigSepM.bigSepM_union (M := Disk.ImageMap) disjoint

theorem flatten_blocks (blocks : BlockMap) (full : BlocksFull blocks) :
    byteLedger view (flatten blocks) ⊣⊢ blockLedger view blocks := by
  induction blocks using LawfulFiniteMap.induction_on (M := Disk.ImageMap) with
  | hemp =>
    simp only [flatten_empty, byteLedger, blockLedger, BigSepM.bigSepM_empty.to_eq]
    exact .rfl
  | hins b bytes blocks absent ih =>
    change blocks[b]? = none at absent
    have bridge : PartialMap.insert (M := Disk.ImageMap) blocks b bytes = blocks.insert b bytes := by
      apply _root_.Std.ExtTreeMap.ext_getElem?
      intro c
      simp [PartialMap.insert, _root_.Std.ExtTreeMap.getElem?_alter, _root_.Std.ExtTreeMap.getElem?_insert]
    rw [bridge] at full ⊢
    have len : bytes.length = 1024 := full b bytes (by simp)
    have rest : BlocksFull blocks := by
      intro c other found
      apply full c other
      have ne : b ≠ c := by intro eq; subst c; rw [absent] at found; cases found
      simpa [_root_.Std.ExtTreeMap.getElem?_insert, ne] using found
    rw [flatten_insert blocks b bytes absent (dbytesOK_full _ full)]
    rw [(byteLedger_union view _ _ (byteRun_flatten_disjoint blocks b bytes
      (dbytesOK_full _ rest) (Nat.le_of_eq len) absent)).to_eq]
    rw [← (blockOwned_run view b bytes len).to_eq, (ih rest).to_eq]
    unfold blockLedger
    rw [← bridge, BigSepM.bigSepM_insert absent |>.to_eq]
    exact .rfl

theorem ledgerSpec : LedgerSpec view where
  run := byteRun_ledger view
  blocks := flatten_blocks view

variable (capacity : Disk.Capacity GF)

theorem imageBytesFull_snapGamma γ gl gt bytes :
    imageBytesFull capacity γ bytes = byteLedger (FsView.snapGamma capacity γ gl gt) bytes := rfl

theorem provided_image_cut γ (whole part : ByteMap)
    (submap : PartialMap.submap (M := Disk.ImageMap) part whole) (frame : IProp GF) :
    imageBytesFull capacity γ whole ∗ frame ⊢ imageBytesFull capacity γ part ∗
      imageBytesFull capacity γ (PartialMap.difference (M := Disk.ImageMap) whole part) ∗ frame := by
  have split := BigSepM.bigSepM_union (M := Disk.ImageMap)
    (Φ := fun a v => Disk.imageByte capacity γ a v)
    (LawfulPartialMap.disjoint_difference_right (M := Disk.ImageMap) (m₁ := whole) (m₂ := part))
  rw [LawfulPartialMap.union_difference_cancel (M := Disk.ImageMap) submap] at split
  unfold imageBytesFull
  iintro ⟨Hbytes, Hframe⟩
  ihave ⟨Hpart, Hrest⟩ := split.mp $$ Hbytes
  iframe Hpart Hrest Hframe

theorem providedImageSpec : ProvidedImageSpec capacity where
  cut := provided_image_cut capacity

end MachCSL.Logic.FsDurBytes
