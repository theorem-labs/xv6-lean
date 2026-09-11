import MachCSL.Logic.FsDurAllocDefs

namespace MachCSL.Logic.FsDurAlloc
open Iris Iris.Std Iris.BI Xv6.Fs DurableState

structure FootprintSpec : Prop where
  slice : ∀ state disk slot, Snapshot.Bytes state disk → Valid state slot →
    PartialMap.submap (M := Disk.ImageMap) (fpMap state disk slot) (FsDurBytes.flatten disk) ∧
      0 ≤ fpOffset slot ∧ fpOffset slot + (fpBytes state disk slot).length ≤ (1024 : Int)
  disjoint : ∀ state disk x y, Snapshot.Bytes state disk → Valid state x → Valid state y → x ≠ y →
    PartialMap.disjoint (M := Disk.ImageMap) (fpMap state disk x) (fpMap state disk y)
  membership : ∀ state slot, Iff (slot ∈ family state) (Valid state slot)
  nodup : ∀ state, (family state).Nodup

structure CarveSpec {GF : BundledGFunctors} (view : FsView.View GF) : Prop where
  carve : ∀ {A : Type} (whole : FsDurBytes.ByteMap) (slots : List A)
    (maps : A → FsDurBytes.ByteMap), slots.Nodup →
    (∀ x, x ∈ slots → PartialMap.submap (M := Disk.ImageMap) (maps x) whole) →
    (∀ x y, x ∈ slots → y ∈ slots → x ≠ y →
      PartialMap.disjoint (M := Disk.ImageMap) (maps x) (maps y)) →
    ∀ frame : IProp GF, FsDurBytes.byteLedger view whole ∗ frame ⊢
      bigSepL (fun _ x => FsDurBytes.byteLedger view (maps x)) slots ∗
      FsDurBytes.byteLedger view (PartialMap.difference (M := Disk.ImageMap) whole (selected slots maps)) ∗ frame
  blocks : ∀ state disk, Snapshot.Bytes state disk → ∀ frame : IProp GF,
    FsDurBytes.blockLedger view disk ∗ frame ⊢ slotLedger view state disk ∗
      FsDurBytes.byteLedger view (PartialMap.difference (M := Disk.ImageMap)
        (FsDurBytes.flatten disk) (selected (family state) (fpMap state disk))) ∗ frame

end MachCSL.Logic.FsDurAlloc
