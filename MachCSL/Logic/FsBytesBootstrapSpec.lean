import MachCSL.Logic.FsBytesBootstrapDefs

namespace MachCSL.Logic.FsBytesBootstrap
open Iris Iris.Std Iris.BI

/-- Native source allocation contracts. Fresh logged-view allocation is distinct
from extension of an existing authority and from physical disk ownership. -/
structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  byte_map_grow : ∀ g (cache : BlockMap) (oldBytes : ByteMap) (oldHome : BlockSet),
    FsDurBytes.BlocksFull cache →
    (∀ b, b ∈ FiniteMap.dom_set (S := BlockSet) cache → b ∉ oldHome) →
    FsBytesInvariant.bytes_dom oldBytes oldHome →
    ∀ frame : IProp GF,
    iprop(⊢ Disk.mapAuth capacity.bytes g oldBytes -∗ frame ==∗ ∃ bytes : ByteMap,
      ⌜FsBytesInvariant.bytes_dom bytes (oldHome ∪ FiniteMap.dom_set (S := BlockSet) cache)⌝ ∗
      ⌜FsBytesInvariant.bytes_tie bytes cache⌝ ∗ Disk.mapAuth capacity.bytes g bytes ∗
      blockRuns capacity g cache ∗ frame)
  fs_bytes_alloc : ∀ (names : Names) (cache : BlockMap) (values : Int → List Byte) (exceptions : BlockSet),
    FsDurBytes.BlocksFull cache →
    (∀ b, b ∈ FiniteMap.dom_set (S := BlockSet) cache → (values b).length = 1024) →
    exceptions ⊆ FiniteMap.dom_set (S := BlockSet) cache →
    (∀ b bytes, get? cache b = some bytes → b ∉ exceptions → values b = bytes) →
    ∀ (E : CoPset) (frame : IProp GF),
    iprop(⊢ FsBytesInvariant.cacheHalves capacity names cache -∗ frame ={E}=∗ ∃ gL gX,
      FsBytesInvariant.invariant capacity (withBytes names gL gX)
        (FiniteMap.dom_set (S := BlockSet) cache) values ∗
      FsBlockGhost.exc_own capacity.blocks gX exceptions ∗
      committedRuns capacity gL cache values ∗ frame)
  fs_alloc : ∀ (link top : GName) (cache : BlockMap) (home : BlockSet)
      (values : Int → List Byte) (exceptions : BlockSet),
    FsDurBytes.BlocksFull cache → home ⊆ FiniteMap.dom_set (S := BlockSet) cache →
    (∀ b, b ∈ home → (values b).length = 1024) → exceptions ⊆ home →
    (∀ b bytes, get? cache b = some bytes → b ∈ home → b ∉ exceptions → values b = bytes) →
    ∀ (E : CoPset) (frame : IProp GF),
    iprop(frame ⊢ |={E}=> ∃ names : Names,
      allocated capacity link top names cache home values exceptions ∗ frame)

end MachCSL.Logic.FsBytesBootstrap
