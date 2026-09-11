import Xv6.Kernel.PtTreeDefs
import Xv6.Kernel.KptLeafDefs
import MachCSL.Logic.EraDefs
import Iris.Algebra.Csum
import Iris.Algebra.Excl
import Iris.Algebra.Agree
import Iris.Std.HeapInstances

/-! The source mapping camera and two distinct one-shot cameras from
`RiscvPtsto.v`, `KMap.v`, `KptGhost.v`, paper pin fa7f0a01.
Camera capacity and runtime names carry no claim of physical tree ownership. -/
namespace MachCSL.Logic.KptGhost
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

abbrev Tree := Xv6.Kernel.PtTree.Tree
abbrev VPN := BitVec 27
abbrev PPN := BitVec 44
abbrev Permission := Xv6.Kernel.KptLeaf.Permission
abbrev Mapping := PPN × Permission
abbrev KeyMap (V : Type) := _root_.Std.ExtTreeMap VPN V
abbrev Map := KeyMap Mapping
abbrev MapRA := HeapView VPN (Agree (DiscreteO Mapping)) KeyMap
abbrev MapRF := constOF MapRA
abbrev TreeRA := Csum (Excl Unit) (Agree (DiscreteO Tree))
abbrev TreeRF := constOF TreeRA
abbrev BoundRA := Csum (Excl Unit) (Agree (DiscreteO Nat))
abbrev BoundRF := constOF BoundRA

def mapFunctor : GFunctor := ⟨MapRF, inferInstance⟩
def treeFunctor : GFunctor := ⟨TreeRF, inferInstance⟩
def boundFunctor : GFunctor := ⟨BoundRF, inferInstance⟩

/-- The log receipt reuses the existing Views capacity, including its exact
shared mono-natural slot. No new log authority is allocated by this layer. -/
structure Capacity (GF : BundledGFunctors) where
  mapping : GhostMapG GF VPN Mapping KeyMap
  tree : ElemG GF TreeRF
  bound : ElemG GF BoundRF
  views : Tso.Views.Capacity GF

structure Names where
  mapping : GName
  tree : GName
  bound : GName
  logLength : GName

def Names.ofEra (era : Era.Record) : Names :=
  ⟨era.kernelMap, era.kernelPageTable, era.kernelPageTableBound, era.logLength⟩

inductive Slot where
  | mapping | tree | bound
  deriving DecidableEq

def Slot.index : Slot → Nat
  | .mapping => 45
  | .tree => 46
  | .bound => 47

/-- The exact source namespace; no invariant body is installed here. -/
def kptN : Namespace := nroot.@("kpt" : String)

def treePending : TreeRA := .inl (.excl ())
def treeShot (t : Tree) : TreeRA := .inr (toAgree ⟨Xv6.Kernel.PtTree.canon t⟩)
def boundPending : BoundRA := .inl (.excl ())
def boundShot (B : Nat) : BoundRA := .inr (toAgree ⟨B⟩)

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Bare full mapping authority: no static-map subset or physical-tree fact. -/
def mapAuth (γ : GName) (M : Map) : IProp GF :=
  letI := capacity.mapping
  ghost_map_auth (H := KeyMap) γ (.own 1) M

/-- The exact source persistent claim, using discarded ownership. -/
def mapAt (γ : GName) (vpn : VPN) (ppn : PPN) (pc : Permission) : IProp GF :=
  letI := capacity.mapping
  ghost_map_elem (H := KeyMap) γ .discard vpn (ppn, pc)

/-- Generic persisted claim bundle. The concrete static source map is a
later instantiation; no guessed classifier or image facts occur here. -/
def allClaims (γ : GName) (M : Map) : IProp GF :=
  bigSepM (M := KeyMap) (fun vpn value => mapAt capacity γ vpn value.1 value.2) M

def unset (γ : GName) : IProp GF := iOwn (E := capacity.tree) γ treePending
def snapshot (γ : GName) (t : Tree) : IProp GF := iOwn (E := capacity.tree) γ (treeShot t)
def boundUnset (γ : GName) : IProp GF := iOwn (E := capacity.bound) γ boundPending

def bound (γ logName : GName) (B : Nat) : IProp GF :=
  iprop(iOwn (E := capacity.bound) γ (boundShot B) ∗ Tso.Views.llb capacity.views logName B)

/-- A fresh camera allocation returns actual resources while reusing the
caller-supplied log name. It does not initialize a machine era. -/
def initial (names : Names) (M : Map) : IProp GF :=
  iprop(mapAuth capacity names.mapping M ∗ allClaims capacity names.mapping M ∗
    unset capacity names.tree ∗ boundUnset capacity names.bound)

end MachCSL.Logic.KptGhost
