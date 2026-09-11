import MachCSL.Logic.FsStateInodeDefs
import MachCSL.Logic.FsStateBitmapDefs

/-! FsState.v's exact nested native filesystem resources. The byte column
uses the selected DFrac; all link ghosts stay whole. Top fragments are external. -/
namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Xv6.Fs FsView
variable {GF : BundledGFunctors} (view : View GF)

def sbOwned (sb : Superblock) (bytes : List (BitVec 8)) : IProp GF :=
  iprop(blockOwned view 1 bytes ∗ ⌜parseSuperblock (fun _ => bytes) = some sb⌝)

variable (capacity : FsLink.Capacity GF)

def fsInodes (sb : Superblock) (nodes : DurableState.InodeMap) : IProp GF :=
  bigSepM (M := InodeMap) (fun i n => inodeOwned view capacity sb i n) nodes

def state (dq : DFrac) (s : DurableState.State) : IProp GF :=
  iprop(sbOwned (gammaQ view dq) s.superblock s.superblockBytes ∗
    fsInodes (gammaQ view dq) capacity s.superblock s.inodes ∗
    freeBitmap (gammaQ view dq) s.superblock s.used ∗ ⌜DurableState.Geometry s⌝)

def footprint (dq : DFrac) (s : DurableState.State) : IProp GF :=
  iprop(blockOwned (gammaQ view dq) 1 s.superblockBytes ∗
    bigSepM (M := InodeMap) (fun i n => inodePhi (gammaQ view dq) s.superblock i n) s.inodes ∗
    blockOwned (gammaQ view dq) s.superblock.bmapstart (BitmapEncoding.bitmapBytes 1024 s.used) ∗
    freePool (gammaQ view dq) s.superblock.size s.used)

def ghost (s : DurableState.State) : IProp GF :=
  iprop(⌜parseSuperblock (fun _ => s.superblockBytes) = some s.superblock⌝ ∗
    bigSepM (M := InodeMap) (fun i n => inodeGhost view capacity i n) s.inodes ∗
    ⌜DurableState.Geometry s⌝)

def pureState (s : DurableState.State) : IProp GF :=
  iprop(⌜parseSuperblock (fun _ => s.superblockBytes) = some s.superblock⌝ ∗
    bigSepM (M := InodeMap) (fun i n => iprop(⌜DurableNode.Local i n⌝)) s.inodes ∗
    ⌜DurableState.Geometry s⌝)

noncomputable def linkNode (γ : GName) (i : Int) (n : Node) : IProp GF :=
  iprop(∃ markers ty types, ⌜LinkFamily.NodeEntOK i n markers ty types⌝ ∗
    iOwn (E := capacity.link) γ (LinkFamily.nodeElem i n ty types))

noncomputable def links (γ : GName) (nodes : DurableState.InodeMap) : IProp GF :=
  bigSepM (M := InodeMap) (fun i n => linkNode capacity γ i n) nodes

end MachCSL.Logic.FsState
