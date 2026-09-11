import MachCSL.Logic.FsViewDefs
import Xv6.Fs.SnapshotHomeDefs
import Iris.Std.HeapInstances

/-! Signed finite byte flattening from LogDefs304/FsDurBytes. The ordered
fold is total, while source correspondence for arbitrary enumeration is
claimed only under the source's per-block length guard. -/
namespace MachCSL.Logic.FsDurBytes
open Iris Iris.Std Iris.BI MachCSL.Memory Xv6.Fs

abbrev ByteMap := Disk.ImageMap Byte
abbrev BlockMap := DurableState.BlockMap

def byteRun (start : Int) (bytes : List Byte) : ByteMap :=
  FiniteMap.map_seqZ (M := Disk.ImageMap) start bytes

def leftUnion (left right : ByteMap) : ByteMap :=
  PartialMap.union (M := Disk.ImageMap) left right

def flattenList (entries : List (Int × List Byte)) : ByteMap :=
  entries.foldr (fun entry acc => leftUnion (byteRun (entry.1 * 1024) entry.2) acc) ∅

def flatten (blocks : BlockMap) : ByteMap :=
  flattenList (FiniteMap.toList (M := Disk.ImageMap) blocks)

def DbytesOK (blocks : BlockMap) : Prop :=
  ∀ (b : Int) (bytes : List Byte), blocks[b]? = some bytes → bytes.length ≤ 1024

def BlocksFull (blocks : BlockMap) : Prop :=
  ∀ (b : Int) (bytes : List Byte), blocks[b]? = some bytes → bytes.length = 1024

variable {GF : BundledGFunctors}

def byteLedger (view : FsView.View GF) (bytes : ByteMap) : IProp GF :=
  bigSepM (M := Disk.ImageMap) (fun a v => view.phi (.own 1) a v) bytes

def blockLedger (view : FsView.View GF) (blocks : BlockMap) : IProp GF :=
  bigSepM (M := Disk.ImageMap) (fun b bytes => FsView.blockOwned view b bytes) blocks

def imageBytesFull (capacity : Disk.Capacity GF) (γ : GName) (bytes : ByteMap) : IProp GF :=
  bigSepM (M := Disk.ImageMap) (fun a v => Disk.imageByte capacity γ a v) bytes

/-- Exact source snap_auth identity: the authority may name a submap of the
committed byte view. Equality and full-map coverage are not silently added. -/
def snapAuth (capacity : Disk.Capacity GF) (γ : GName) (blocks : BlockMap) : IProp GF :=
  iprop(∃ bytes : ByteMap, Disk.mapAuth capacity γ bytes ∗
    ⌜PartialMap.submap (M := Disk.ImageMap) bytes (flatten blocks)⌝)

end MachCSL.Logic.FsDurBytes
