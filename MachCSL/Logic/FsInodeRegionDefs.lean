import MachCSL.Logic.FsViewDefs
import MachCSL.Logic.FsStateInodeDefs
import Xv6.Fs.InodeRegionImageDefs
import Iris.Std.HeapInstances

/-! Exact iregG record camera, marker cells, initial maps and byte rows.
The full inode-region slot and invariant remain separate source dependencies. -/
namespace MachCSL.Logic.FsInodeRegion
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI Xv6.Fs SnapshotConfig

abbrev RecordMap (V : Type) := _root_.Std.ExtTreeMap Int V
abbrev RecordRA := HeapView Int (Agree (DiscreteO Dinode)) RecordMap
abbrev RecordRF := constOF RecordRA
def recordFunctor : GFunctor := ⟨RecordRF, inferInstance⟩
structure Capacity (GF : BundledGFunctors) where
  record : GhostMapG GF Int Dinode RecordMap

variable {GF : BundledGFunctors} (capacity : Capacity GF)
def authQ (g : GName) (dq : DFrac) (records : RecordMap Dinode) : IProp GF :=
  letI := capacity.record
  ghost_map_auth (H := RecordMap) g dq records
def auth (g : GName) (records : RecordMap Dinode) : IProp GF := authQ capacity g (.own 1) records
def fragQ (g : GName) (dq : DFrac) (i : Int) (record : Dinode) : IProp GF :=
  letI := capacity.record
  ghost_map_elem g dq i record
def frag (g : GName) (i : Int) (record : Dinode) : IProp GF := fragQ capacity g (.own 1) i record

def dinodeAt (g : GName) (inum : BitVec 32) (record : Dinode) : IProp GF :=
  frag capacity g inum.toNat record

def markKey (i : Int) : Int := -(i + 1)
def imark (g : GName) (i : Int) : IProp GF := iprop(∃ record : Dinode, frag capacity g (markKey i) record)
def out (g : GName) (inum : BitVec 32) (record : Dinode) : IProp GF :=
  if record.typeZ = 0 then imark capacity g inum.toNat else dinodeAt capacity g inum record

def markRecord : Dinode := ⟨0, 0, 0, 0, 0, []⟩
def markInums (nib : Nat) : BlockSet :=
  _root_.Std.ExtTreeSet.ofList ((List.range (16 * nib)).map (fun i => markKey (Int.ofNat i)))
def initialRecords (records : List (List Dinode)) (nib : Nat) : RecordMap Dinode :=
  FiniteMap.ofSetWith (M := RecordMap) (InodeRegionImage.imageDinode records) (regionInums nib)
def initialMarkers (nib : Nat) : RecordMap Dinode :=
  FiniteMap.ofSetWith (M := RecordMap) (fun _ => markRecord) (markInums nib)
def initialMap (records : List (List Dinode)) (nib : Nat) : RecordMap Dinode :=
  PartialMap.union (M := RecordMap) (initialRecords records nib) (initialMarkers nib)

def allFragments (g : GName) (records : RecordMap Dinode) : IProp GF :=
  bigSepM (M := RecordMap) (fun i record => frag capacity g i record) records

def couple (records : RecordMap Dinode) (bi : Nat) (block : List Dinode) : Prop :=
  ∀ i : Nat, i < 16 → records[16 * (bi : Int) + (i : Int)]? = some (block[i]?.getD default)

def recs (view : FsView.View GF) (start : Int) (bi : Nat) (records : List Dinode) : IProp GF :=
  bigSepL (fun _ (i : Nat) => FsState.recOwnedAt view start (16 * (bi : Int) + (i : Int)) (records[i]?.getD default)) (List.range 16)

/-- All original full record and marker elements; routing into the complete
slot/out partition is not hidden inside this allocation prelude. -/
def bootCells (g : GName) (records : List (List Dinode)) (nib : Nat) : IProp GF :=
  bigSepS (fun i => iprop(dinodeAt capacity g (BitVec.ofInt 32 i) (InodeRegionImage.imageDinode records i) ∗ imark capacity g i)) (regionInums nib)

end MachCSL.Logic.FsInodeRegion
