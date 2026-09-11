import MachCSL.Logic.FsLinkDefs
import MachCSL.Logic.FsTopDefs
import Xv6.Fs.InodeRegionImageDefs

/-! Source InodeRegion's per-inode authority and guarded top-fragment park.
The root singleton is a real native fragment, separate from entry payloads. -/
namespace MachCSL.Logic.IcacheInodeCustody
open Iris Iris.Std Iris.BI Xv6.Fs

def freeNode (d : Dinode) : DurableNode.Node :=
  ⟨d, List.replicate 256 0, ∅⟩

abbrev ireg_bare := InodeRegionImage.bare
abbrev ireg_nl := InodeRegionImage.nlink

def ireg_mult_at (n : Nat) (ty : Int) : Nat :=
  n + if ty = 1 ∧ n ≠ 0 then 1 else 0

def ireg_mult (d : Dinode) : Nat := ireg_mult_at (ireg_nl d) d.typeZ

def ireg_dot_delta (ty n : Int) : Nat := if ty = 1 ∧ n = 0 then 2 else 1

def ireg_reg_ok (ty : Int) : FsLink.IType → Prop
  | .file => ty ≠ 1
  | .directory _ => ty = 1

variable {GF : BundledGFunctors} (view : FsView.View GF)
    (links : FsLink.Capacity GF)

def ireg_keep (z : Int) (v : FsLink.IType) : IProp GF :=
  if z = 1 then FsLink.tok links view.link z v else iprop(emp)

def ireg_lnk_at (z : Int) (n : Nat) (ty : Int) : IProp GF :=
  iprop(∃ v, ⌜ireg_reg_ok ty v⌝ ∗
    FsLink.auth links view.link z (ireg_mult_at n ty) v ∗ ireg_keep view links z v)

def ireg_lnk (z : Int) (d : Dinode) : IProp GF :=
  ireg_lnk_at view links z (ireg_nl d) d.typeZ

def ireg_top_park (tops : FsTop.Capacity GF) (z : Int) (d : Dinode) : IProp GF :=
  iprop(∃ n, ⌜d.typeZ = 0 → ireg_bare d ∧ n = freeNode d⌝ ∗
    FsTop.topFrag tops view z n)

end MachCSL.Logic.IcacheInodeCustody
