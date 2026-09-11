import MachCSL.Logic.FsBlockGhostDefs
import MachCSL.Logic.FsDurBytesDefs
import Iris.Instances.Lib.Invariants

/-! Exact nine-leg FsBlocks byte/cache/exception invariant and source client rows. -/
namespace MachCSL.Logic.FsBytesInvariant
open Iris Iris.Std Iris.BI

abbrev Byte := BitVec 8
abbrev ByteMap := Disk.ImageMap Byte
abbrev CacheMap := FsBlockGhost.BlockMap (List Byte)
abbrev BlockSet := FsBlockGhost.ExceptionSet
abbrev Names := FsBlocks.Names

structure Capacity (GF : BundledGFunctors) where
  blocks : FsBlockGhost.Capacity GF
  bytes : Disk.Capacity GF

def logN : Namespace := nroot.@("fslogbytes" : String)
def fsbN : Namespace := logN.@("b" : String)

def bytes_dom (logged : ByteMap) (home : BlockSet) : Prop :=
  ∀ address : Int, (get? logged address).isSome ↔
    ∃ block : Int, block ∈ home ∧ block * 1024 ≤ address ∧ address < block * 1024 + 1024

def bytes_tie (logged : ByteMap) (cache : CacheMap) : Prop :=
  ∀ block bytes, get? cache block = some bytes →
    PartialMap.submap (FsDurBytes.byteRun (block * 1024) bytes) logged

def bytes_tie_exc (logged : ByteMap) (cache : CacheMap) (exceptions : BlockSet) : Prop :=
  ∀ block bytes, get? cache block = some bytes → block ∉ exceptions →
    PartialMap.submap (FsDurBytes.byteRun (block * 1024) bytes) logged

def bytes_exc_val (logged : ByteMap) (values : Int → List Byte) (exceptions : BlockSet) : Prop :=
  ∀ block, block ∈ exceptions → PartialMap.submap (FsDurBytes.byteRun (block * 1024) (values block)) logged

variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)

def cacheHalves (cache : CacheMap) : IProp GF :=
  bigSepM (M := FsBlockGhost.BlockMap) (fun block bytes => FsBlockGhost.chalf capacity.blocks names block bytes) cache

def body (home : BlockSet) (values : Int → List Byte) : IProp GF :=
  iprop(∃ (logged : ByteMap) (cache : CacheMap) (exceptions : BlockSet),
    Disk.mapAuth capacity.bytes names.bytes logged ∗
    cacheHalves capacity names cache ∗ FsBlockGhost.exc_auth capacity.blocks names.exceptions exceptions ∗
    ⌜FiniteMap.dom_set (S := BlockSet) cache = home⌝ ∗
    ⌜∀ block bytes, get? cache block = some bytes → bytes.length = 1024⌝ ∗
    ⌜bytes_tie_exc logged cache exceptions⌝ ∗ ⌜bytes_dom logged home⌝ ∗
    ⌜exceptions ⊆ home⌝ ∗ ⌜bytes_exc_val logged values exceptions⌝)

variable {hlc : HasLC} [InvGS_gen hlc GF]

def invariant (home : BlockSet) (values : Int → List Byte) : IProp GF :=
  inv fsbN (body capacity names home values)
def atHome (home : BlockSet) : IProp GF :=
  iprop(∃ values : Int → List Byte, invariant capacity names home values)
def row : IProp GF := iprop(∃ home : BlockSet, atHome capacity names home)
def any : IProp GF := iprop(row capacity names ∗ FsBlockGhost.exc_sealed capacity.blocks names.exceptions)
def anyAt (home : BlockSet) : IProp GF :=
  iprop(atHome capacity names home ∗ FsBlockGhost.exc_sealed capacity.blocks names.exceptions)

end MachCSL.Logic.FsBytesInvariant
