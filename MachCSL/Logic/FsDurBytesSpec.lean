import MachCSL.Logic.FsDurBytesDefs

namespace MachCSL.Logic.FsDurBytes
open Iris Iris.Std Iris.BI MachCSL.Memory

structure FlattenSpec : Prop where
  lookup : ∀ (blocks : BlockMap) (a : Int) (v : Byte), DbytesOK blocks →
    Iff ((flatten blocks)[a]? = some v)
      (∃ (b : Int) (bytes : List Byte) (k : Nat),
        blocks[b]? = some bytes ∧ bytes[k]? = some v ∧ a = b * 1024 + (k : Int))
  enumeration : ∀ blocks entries, DbytesOK blocks →
    entries.Perm (FiniteMap.toList (M := Disk.ImageMap) blocks) → flattenList entries = flatten blocks

structure LedgerSpec {GF : BundledGFunctors} (view : FsView.View GF) : Prop where
  run : ∀ start bytes, byteLedger view (byteRun start bytes) ⊣⊢ FsView.byteRange view 0 start bytes
  blocks : ∀ blocks, BlocksFull blocks → byteLedger view (flatten blocks) ⊣⊢ blockLedger view blocks

structure ProvidedImageSpec {GF : BundledGFunctors} (capacity : Disk.Capacity GF) : Prop where
  cut : ∀ γ (whole part : ByteMap), PartialMap.submap (M := Disk.ImageMap) part whole →
    ∀ frame : IProp GF,
      imageBytesFull capacity γ whole ∗ frame ⊢
        imageBytesFull capacity γ part ∗
          imageBytesFull capacity γ (PartialMap.difference (M := Disk.ImageMap) whole part) ∗ frame

end MachCSL.Logic.FsDurBytes
