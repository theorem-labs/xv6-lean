import Xv6.Fs.DurableImageNodeDefs
import MachCSL.Logic.FsLinkDefs
import Iris.Algebra.BigOp

/-! Source FsStateInode/FsState pure link elements over the native FsLink camera.
The carrier includes arbitrary durable nodes and full finite inode maps. -/
namespace Xv6.Fs.LinkFamily
open DurableNode MachCSL.Logic.FsLink Iris Iris.CMRA Iris.Algebra

def KindOK (n : Node) (v : IType) : Prop :=
  match v with
  | .file => n.isDir = false
  | .directory _ => n.isDir = true

def multiplicity (n : Node) : Nat :=
  n.nlink + if n.isDir && !n.orphan then 1 else 0

/-- Exact executable exemption, including every nondot self-target. -/
def tokenless (self : Int) (orphan : Bool) (name : FName) (target : Int) : Bool :=
  ((decide (name = dotName) || decide (name = dotdotName)) && orphan) ||
    (decide (target = self) && !decide (name = dotName))

def EntryTypeOK (self : Int) (parent : Option Int) (isDirectory : Bool)
    (name : FName) (ty : IType) : Prop :=
  if name = dotName then ∀ p q, ty = .directory p → parent = some q → q = p
  else if name = dotdotName then True
  else if isDirectory then ty = .directory self else ty = .file

def parentEntry (n : Node) : Option Int := n.dirEntries[dotdotName]?

def MarkersOK (n : Node) (markers : NameSet) : Prop :=
  ∀ name, name ∈ markers → n.dirEntries[name]?.isSome ∧
    name ≠ dotName ∧ name ≠ dotdotName

def ExactCount (n : Node) (markers : NameSet) : Prop :=
  n.isDir = true → n.nlink = markers.size + if n.orphan then 0 else 1

def entryElem (self : Int) (orphan : Bool) (name : FName) (target : Int)
    (ty : IType) : FamilyRA :=
  if tokenless self orphan name target then unit else tokElem target ty

noncomputable def entriesElem (self : Int) (n : Node) (types : FName → IType) : FamilyRA :=
  bigOpM (M' := fun V => Std.ExtTreeMap FName V) CMRA.op
    (fun name target => entryElem self n.orphan name target (types name)) n.dirEntries

noncomputable def nodeElem (self : Int) (n : Node) (value : IType)
    (types : FName → IType) : FamilyRA :=
  authElem self (multiplicity n) value • entriesElem self n types

def NodeEntOK (self : Int) (n : Node) (markers : NameSet) (value : IType)
    (types : FName → IType) : Prop :=
  KindOK n value ∧ MarkersOK n markers ∧ ExactCount n markers ∧
    ∀ name target, n.dirEntries[name]? = some target →
      tokenless self n.orphan name target = false →
      EntryTypeOK self (parentEntry n) (decide (name ∈ markers)) name (types name)

abbrev Choice := Int → NameSet × (IType × (FName → IType))
def choiceMarkers (f : Choice) (i : Int) : NameSet := (f i).1
def choiceValue (f : Choice) (i : Int) : IType := (f i).2.1
def choiceTypes (f : Choice) (i : Int) : FName → IType := (f i).2.2

def ElemOK (nodes : DurableState.InodeMap) (f : Choice) : Prop :=
  ∀ i n, nodes[i]? = some n → NodeEntOK i n (choiceMarkers f i)
    (choiceValue f i) (choiceTypes f i)

noncomputable def elem (nodes : DurableState.InodeMap) (f : Choice) : FamilyRA :=
  bigOpM (M' := MachCSL.Logic.FsLink.FamilyMap) CMRA.op
    (fun i n => nodeElem i n (choiceValue f i) (choiceTypes f i)) nodes

/-- Source img_v and img_f are total, including keys outside the inode map. -/
def imageValue (image : Blocks) (sb : Superblock) (i : Int) : IType :=
  if (DurableImageNode.imageNode image sb i).isDir then .directory 1 else .file

def imageChoice (image : Blocks) (sb : Superblock) : Choice := fun i =>
  (∅, (imageValue image sb i, fun name =>
    match (DurableImageNode.imageNode image sb i).dirEntries[name]? with
    | some target => imageValue image sb target
    | none => .file))

end Xv6.Fs.LinkFamily
