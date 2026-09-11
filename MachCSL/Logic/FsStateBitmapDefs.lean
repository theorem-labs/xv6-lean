import MachCSL.Logic.FsViewDefs
import Xv6.Fs.BitmapEncodingDefs

/-! Exact FsStateBitmap resources: the signed block count bounds a pool
whose clear-bit slots own arbitrary full blocks, including block zero. -/
namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Xv6.Fs FsView
variable {GF : BundledGFunctors} (view : View GF)

def poolElt (used : BlockSet) (b : Int) : IProp GF :=
  if b ∈ used then emp else iprop(∃ bytes, blockOwned view b bytes)

/-- Source seqZ 0 nb, including the empty sequence when nb is negative. -/
def poolIndices (nb : Int) : List Int := (List.range nb.toNat).map Int.ofNat

def freePool (nb : Int) (used : BlockSet) : IProp GF :=
  iprop([∗list] b ∈ poolIndices nb, poolElt view used b)
def freePoolBut (nb : Int) (used : BlockSet) (i0 : Nat) : IProp GF :=
  iprop([∗list] k ↦ b ∈ poolIndices nb, if k = i0 then emp else poolElt view used b)

def freeBitmapAt (bitmapBlock nb : Int) (used : BlockSet) : IProp GF :=
  iprop(blockOwned view bitmapBlock (BitmapEncoding.bitmapBytes 1024 used) ∗ freePool view nb used)
def freeBitmap (sb : Superblock) (used : BlockSet) : IProp GF :=
  freeBitmapAt view sb.bmapstart sb.size used

end MachCSL.Logic.FsState
