import MachCSL.Logic.FsViewDefs
import Xv6.Fs.LinkFamilyDefs
import Iris.Std.HeapInstances

/-! Native nested inode resources from FsStateInode.v. The arbitrary source
node carrier and every stored block are retained; top-map fragments are separate. -/
namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Xv6.Fs FsView

abbrev Node := DurableNode.Node
abbrev SlotMap (V : Type) := _root_.Std.ExtTreeMap Nat V
abbrev EntryMap (V : Type) := _root_.Std.ExtTreeMap FName V
abbrev InodeMap (V : Type) := _root_.Std.ExtTreeMap Int V

variable {GF : BundledGFunctors} (view : View GF)

def recOwnedQ (dq : DFrac) (sb : Superblock) (i : Int) (dn : Dinode) : IProp GF :=
  byteRangeQ view dq (inodeBlock (BitVec.ofInt 32 i) sb.inodestart)
    (64 * inodeSlot (BitVec.ofInt 32 i)) (dinodeBytes dn)
def recOwned (sb : Superblock) (i : Int) (dn : Dinode) : IProp GF :=
  recOwnedQ view (.own 1) sb i dn

def recOwnedAtQ (dq : DFrac) (istart z : Int) (dn : Dinode) : IProp GF :=
  byteRangeQ view dq (istart + z / 16) (64 * (z % 16)) (dinodeBytes dn)
def recOwnedAt (istart z : Int) (dn : Dinode) : IProp GF :=
  recOwnedAtQ view (.own 1) istart z dn

def indOwnedQ (dq : DFrac) (n : Node) : IProp GF :=
  if n.indirect = 0 then emp else blockOwnedQ view dq n.indirect (indirectBytes n.entries)
def indOwned (n : Node) : IProp GF := indOwnedQ view (.own 1) n

def inodeDatQ (dq : DFrac) (n : Node) : IProp GF :=
  iprop(bigSepM (M := SlotMap) (fun k bs => blockOwnedQ view dq (n.address k) bs) n.blocks
    ∗ indOwnedQ view dq n)
def inodeDat (n : Node) : IProp GF := inodeDatQ view (.own 1) n

def inodePhi (sb : Superblock) (i : Int) (n : Node) : IProp GF :=
  iprop(recOwned view sb i n.record ∗ inodeDat view n)
def inodePhiAt (istart z : Int) (n : Node) : IProp GF :=
  iprop(recOwnedAt view istart z n.record ∗ inodeDat view n)

variable (capacity : FsLink.Capacity GF)

def entTokAt (self : Int) (orphan : Bool) (name : FName) (target : Int)
    (ty : FsLink.IType) : IProp GF :=
  if LinkFamily.tokenless self orphan name target then emp
  else FsLink.tok capacity view.link target ty

def entTok (self : Int) (parent : Option Int) (orphan isDirectory : Bool)
    (name : FName) (target : Int) : IProp GF :=
  if LinkFamily.tokenless self orphan name target then emp
  else iprop(∃ ty, FsLink.tok capacity view.link target ty ∗
    ⌜LinkFamily.EntryTypeOK self parent isDirectory name ty⌝)

def entToks (i : Int) (n : Node) (markers : NameSet) : IProp GF :=
  bigSepM (M := EntryMap) (fun name target => entTok view capacity i
    (LinkFamily.parentEntry n) n.orphan (decide (name ∈ markers)) name target) n.dirEntries

def entToksNodot (i : Int) (n : Node) (markers : NameSet) : IProp GF :=
  bigSepM (M := EntryMap) (fun name target => entTok view capacity i
    (LinkFamily.parentEntry n) n.orphan (decide (name ∈ markers)) name target)
    (n.dirEntries.erase dotName)

def entToksX (i : Int) (n : Node) : IProp GF :=
  iprop(∃ markers, ⌜LinkFamily.MarkersOK n markers⌝ ∗
    ⌜LinkFamily.ExactCount n markers⌝ ∗ entToks view capacity i n markers)

def inodeGhost (i : Int) (n : Node) : IProp GF :=
  iprop(∃ ty, ⌜LinkFamily.KindOK n ty⌝ ∗
    FsLink.auth capacity view.link i (LinkFamily.multiplicity n) ty ∗
    entToksX view capacity i n ∗ ⌜DurableNode.Local i n⌝)

def inodeOwned (sb : Superblock) (i : Int) (n : Node) : IProp GF :=
  iprop(inodePhi view sb i n ∗ inodeGhost view capacity i n)

end MachCSL.Logic.FsState
