import MachCSL.Logic.FsBlocksBytesDefs
import Iris.Std.HeapInstances
import MachCSL.Logic.FsBlockGhostKey

/-! Exact fsLogG cache/dirty/exception cameras and FsBlocks resource predicates.
The byte view continues to use the existing Disk camera, outside this capacity. -/
namespace MachCSL.Logic.FsBlockGhost
open Iris Iris.Std Iris.Algebra Iris.BI
open scoped MachCSL.Logic.FsBlockGhost.Key

abbrev Byte := BitVec 8
abbrev Names := FsBlocks.Names
abbrev BlockMap (V : Type) := _root_.Std.ExtTreeMap Int V
abbrev ExceptionSet := _root_.Std.ExtTreeSet Int
abbrev ExceptionMap (V : Type) := _root_.Std.ExtTreeMap Unit V
abbrev CacheRA := HeapView Int (Agree (DiscreteO (List Byte))) BlockMap
abbrev DirtyRA := HeapView Int (Agree (DiscreteO Bool)) BlockMap
abbrev ExceptionRA := HeapView Unit (Agree (DiscreteO ExceptionSet)) ExceptionMap
abbrev CacheRF := constOF CacheRA
abbrev DirtyRF := constOF DirtyRA
abbrev ExceptionRF := constOF ExceptionRA
def cacheFunctor : GFunctor := ⟨CacheRF, inferInstance⟩
def dirtyFunctor : GFunctor := ⟨DirtyRF, inferInstance⟩
def exceptionFunctor : GFunctor := ⟨ExceptionRF, inferInstance⟩

structure Capacity (GF : BundledGFunctors) where
  cache : GhostMapG GF Int (List Byte) BlockMap
  dirty : GhostMapG GF Int Bool BlockMap
  exceptions : GhostMapG GF Unit ExceptionSet ExceptionMap

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def cacheAuth (names : Names) (cache : BlockMap (List Byte)) : IProp GF :=
  letI := capacity.cache
  ghost_map_auth names.cache (.own 1) cache
def dirtyAuth (names : Names) (dirty : BlockMap Bool) : IProp GF :=
  letI := capacity.dirty
  ghost_map_auth names.dirty (.own 1) dirty
def cacheElem (names : Names) (dq : DFrac) (block : Int) (bytes : List Byte) : IProp GF :=
  letI := capacity.cache
  ghost_map_elem names.cache dq block bytes
def dirtyElem (names : Names) (dq : DFrac) (block : Int) (dirty : Bool) : IProp GF :=
  letI := capacity.dirty
  ghost_map_elem names.dirty dq block dirty

def chalf (names : Names) (block : Int) (bytes : List Byte) : IProp GF :=
  cacheElem capacity names (.own (1 : Qp).half) block bytes
def dirtyHalf (names : Names) (block : Int) (dirty : Bool) : IProp GF :=
  dirtyElem capacity names (.own (1 : Qp).half) block dirty
def mclean (names : Names) (block : Int) (bytes : List Byte) : IProp GF :=
  iprop(chalf capacity names block bytes ∗ dirtyHalf capacity names block false)
def mdirty (names : Names) (block : Int) (bytes : List Byte) : IProp GF :=
  iprop(chalf capacity names block bytes ∗ dirtyHalf capacity names block true)

def exc_auth (g : GName) (exceptions : ExceptionSet) : IProp GF :=
  letI := capacity.exceptions
  ghost_map_auth g (.own 1) (PartialMap.singleton () exceptions : ExceptionMap ExceptionSet)
def exc_own (g : GName) (exceptions : ExceptionSet) : IProp GF :=
  letI := capacity.exceptions
  ghost_map_elem g (.own 1) () exceptions
def exc_sealed (g : GName) : IProp GF :=
  letI := capacity.exceptions
  ghost_map_elem g .discard () (∅ : ExceptionSet)

end MachCSL.Logic.FsBlockGhost
