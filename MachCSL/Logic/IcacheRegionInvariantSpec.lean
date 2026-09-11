import MachCSL.Logic.IcacheRegionInvariantDefs

namespace MachCSL.Logic.IcacheRegionInvariant
open Iris Iris.BI

structure Spec {GF : BundledGFunctors} {hlc : HasLC} [InvGS_gen hlc GF]
    (capacity : Capacity GF) : Prop where
  ireg_inv_reg : ∀ names records start nib,
    iprop(⊢ ireg_inv capacity names records start nib -∗ ireg_reg capacity names records start nib)
  ireg_inv_of : ∀ names records start nib,
    iprop(⊢ ireg_reg capacity names records start nib -∗
      FsBlockGhost.exc_sealed capacity.blocks names.filesystem.exceptions -∗
      ireg_inv capacity names records start nib)
  ireg_inv_bytes : ∀ names records start nib,
    iprop(⊢ ireg_inv capacity names records start nib -∗
      FsBytesInvariant.any (byteCapacity capacity) names.filesystem)
  ireg_inv_ftop : ∀ names records start nib,
    iprop(⊢ ireg_inv capacity names records start nib -∗ topInvariant capacity names)
  allocate : ∀ names records start nib (E : CoPset) (frame : IProp GF),
    iprop(⊢ body capacity names records start nib -∗
      FsBytesInvariant.row (byteCapacity capacity) names.filesystem -∗ topInvariant capacity names -∗
      frame ={E}=∗ ireg_reg capacity names records start nib ∗ frame)

end MachCSL.Logic.IcacheRegionInvariant
