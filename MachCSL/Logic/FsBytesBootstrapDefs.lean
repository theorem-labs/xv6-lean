import MachCSL.Logic.FsBytesInvariantDefs
import MachCSL.Logic.FsBytesGammaDefs

/-! Exact source block/byte mint data and complete ownership outputs. -/
namespace MachCSL.Logic.FsBytesBootstrap
open Iris Iris.Std Iris.BI

abbrev Capacity := FsBytesInvariant.Capacity
abbrev Names := FsBlocks.Names
abbrev Byte := BitVec 8
abbrev ByteMap := FsBytesInvariant.ByteMap
abbrev BlockMap := FsBytesInvariant.CacheMap
abbrev BlockSet := FsBytesInvariant.BlockSet

/-- The original key domain is retained, including present empty values. -/
def valueMap (cache : BlockMap) (values : Int → List Byte) : BlockMap :=
  Iris.Std.PartialMap.bindAlter (fun b (_ : List Byte) => some (values b)) cache

def cleanMap (cache : BlockMap) : FsBlockGhost.BlockMap Bool :=
  Iris.Std.PartialMap.map (fun _ : List Byte => false) cache

def homeMap (cache : BlockMap) (home : BlockSet) : BlockMap :=
  PartialMap.filter (fun b _ => decide (b ∈ home)) cache

def outsideMap (cache : BlockMap) (home : BlockSet) : BlockMap :=
  PartialMap.filter (fun b _ => decide (b ∉ home)) cache

def withBytes (names : Names) (bytes exceptions : GName) : Names :=
  { names with bytes := bytes, exceptions := exceptions }

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def blockRuns (g : GName) (cache : BlockMap) : IProp GF :=
  bigSepM (M := FsBlockGhost.BlockMap) (fun b bytes => FsBlocks.block capacity.bytes g b bytes) cache

/-- Indexed by the raw map's actual domain, with the committed payload at each key. -/
def committedRuns (g : GName) (cache : BlockMap) (values : Int → List Byte) : IProp GF :=
  bigSepM (M := FsBlockGhost.BlockMap) (fun b _ => FsBlocks.block capacity.bytes g b (values b)) cache

/-- Both machinery's half and the log's second dirty half remain explicit. -/
def machinery (names : Names) (cache : BlockMap) : IProp GF :=
  bigSepM (M := FsBlockGhost.BlockMap)
    (fun b bytes => iprop(FsBlockGhost.mclean capacity.blocks names b bytes ∗
      FsBlockGhost.dirtyHalf capacity.blocks names b false)) cache

variable {hlc : HasLC} [InvGS_gen hlc GF]

/-- Complete source fs_alloc result, before any consumer distribution.
The exception handle is not silently converted to a recovery seal. -/
def allocated (link top : GName) (names : Names) (cache : BlockMap)
    (home : BlockSet) (values : Int → List Byte) (exceptions : BlockSet) : IProp GF :=
  iprop(⌜names.link = link⌝ ∗ ⌜names.top = top⌝ ∗
    FsBlockGhost.cacheAuth capacity.blocks names cache ∗
    FsBlockGhost.dirtyAuth capacity.blocks names (cleanMap cache) ∗
    FsBytesInvariant.invariant capacity names home values ∗
    FsBlockGhost.exc_own capacity.blocks names.exceptions exceptions ∗
    machinery capacity names cache ∗
    committedRuns capacity names.bytes (homeMap cache home) values ∗
    FsBytesInvariant.cacheHalves capacity names (outsideMap cache home))

end MachCSL.Logic.FsBytesBootstrap
