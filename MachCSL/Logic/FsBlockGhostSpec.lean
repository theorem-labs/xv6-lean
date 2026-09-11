import MachCSL.Logic.FsBlockGhostDefs

namespace MachCSL.Logic.FsBlockGhost
open Iris Iris.Std Iris.BI

structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  clean_agree : ∀ names block bytes machinery,
    iprop(⊢ chalf capacity names block bytes -∗ mclean capacity names block machinery -∗ ⌜machinery = bytes⌝)
  dirty_agree : ∀ names block bytes machinery,
    iprop(⊢ chalf capacity names block bytes -∗ mdirty capacity names block machinery -∗ ⌜machinery = bytes⌝)
  cache_update : ∀ names (cache : BlockMap (List Byte)) block bytes new machinery,
    iprop(⊢ cacheAuth capacity names cache -∗ chalf capacity names block bytes -∗
      chalf capacity names block machinery ==∗
      ⌜machinery = bytes ∧ get? cache block = some bytes⌝ ∗
      cacheAuth capacity names (PartialMap.insert cache block new) ∗
      chalf capacity names block new ∗ chalf capacity names block new)
  dirty_flip : ∀ names (dirty : BlockMap Bool) block value other new,
    iprop(⊢ dirtyAuth capacity names dirty -∗ dirtyHalf capacity names block value -∗
      dirtyHalf capacity names block other ==∗
      ⌜other = value ∧ get? dirty block = some value⌝ ∗
      dirtyAuth capacity names (PartialMap.insert dirty block new) ∗
      dirtyHalf capacity names block new ∗ dirtyHalf capacity names block new)
  exception_allocate : ∀ exceptions (frame : IProp GF),
    iprop(frame ⊢ |==> ∃ g, exc_auth capacity g exceptions ∗ exc_own capacity g exceptions ∗ frame)
  exception_agree : ∀ g left right,
    iprop(⊢ exc_auth capacity g left -∗ exc_own capacity g right -∗ ⌜left = right⌝)
  sealed_empty : ∀ g exceptions,
    iprop(⊢ exc_auth capacity g exceptions -∗ exc_sealed capacity g -∗ ⌜exceptions = ∅⌝)
  exception_update : ∀ g old new,
    iprop(⊢ exc_auth capacity g old -∗ exc_own capacity g old ==∗
      exc_auth capacity g new ∗ exc_own capacity g new)
  exception_seal : ∀ g, iprop(exc_own capacity g ∅ ⊢ |==> exc_sealed capacity g)

end MachCSL.Logic.FsBlockGhost
