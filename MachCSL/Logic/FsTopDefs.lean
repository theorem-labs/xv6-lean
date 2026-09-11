import MachCSL.Logic.FsViewDefs
import Xv6.Fs.DurableStateDefs
import Iris.Std.HeapInstances

/-! Native top inode map from `Xv6Cameras.fsTopG` and `FsState.top_frag`.
Values are the complete arbitrary durable nodes; validity is not part of
the carrier or a precondition of camera allocation. -/
namespace MachCSL.Logic.FsTop
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

abbrev Node := Xv6.Fs.DurableNode.Node
abbrev TopMap (V : Type) := _root_.Std.ExtTreeMap Int V
abbrev TopRA := HeapView Int (Agree (DiscreteO Node)) TopMap
abbrev TopRF := constOF TopRA
def topFunctor : GFunctor := ⟨TopRF, inferInstance⟩

structure Capacity (GF : BundledGFunctors) where
  top : GhostMapG GF Int Node TopMap

variable {GF : BundledGFunctors} (capacity : Capacity GF)

def authQ (γ : GName) (dq : DFrac) (nodes : Xv6.Fs.DurableState.InodeMap) : IProp GF :=
  letI := capacity.top
  ghost_map_auth (H := TopMap) γ dq nodes

def auth (γ : GName) (nodes : Xv6.Fs.DurableState.InodeMap) : IProp GF :=
  authQ capacity γ (.own 1) nodes

def fragQ (γ : GName) (dq : DFrac) (i : Int) (node : Node) : IProp GF :=
  letI := capacity.top
  ghost_map_elem γ dq i node

def frag (γ : GName) (i : Int) (node : Node) : IProp GF :=
  fragQ capacity γ (.own 1) i node

def allFragments (γ : GName) (nodes : Xv6.Fs.DurableState.InodeMap) : IProp GF :=
  bigSepM (M := TopMap) (fun i node => frag capacity γ i node) nodes

/-- The source's view-indexed API, with the runtime top name kept explicit. -/
def topFragQ (view : FsView.View GF) (dq : DFrac) (i : Int) (node : Node) : IProp GF :=
  fragQ capacity view.top dq i node

def topFrag (view : FsView.View GF) (i : Int) (node : Node) : IProp GF :=
  topFragQ capacity view (.own 1) i node

end MachCSL.Logic.FsTop
