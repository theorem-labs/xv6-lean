import MachCSL.Logic.IcacheRegionInvariantSpec
import MachCSL.Logic.FsBytesInvariantRowsProofs
import MachCSL.Logic.IcacheTopRegistryProofs

namespace MachCSL.Logic.IcacheRegionInvariant
open Iris Iris.BI
variable {GF : BundledGFunctors} (capacity : Capacity GF) (names : Names)

theorem view_bytes : (view capacity names).phi = FsBlocks.byteElem capacity.bytes names.filesystem.bytes := rfl
theorem view_link : (view capacity names).link = names.filesystem.link := rfl
theorem view_top : (view capacity names).top = names.filesystem.top := rfl
theorem top_same : (topNames names).top = (view capacity names).top := rfl
theorem transactions_same : (topNames names).transactions = names.region.transactions := rfl
theorem top_capacity_same : (topCapacity capacity).top = capacity.region.tops := rfl
theorem transactions_capacity_same : (topCapacity capacity).transactions = capacity.region.transactions := rfl
theorem bytes_capacity_same : (byteCapacity capacity).bytes = capacity.bytes := rfl

variable {hlc : HasLC} [InvGS_gen hlc GF]

instance topInvariant_persistent : Persistent (topInvariant capacity names) := by
  unfold topInvariant
  infer_instance
instance ireg_reg_persistent records start nib : Persistent (ireg_reg capacity names records start nib) := by
  unfold ireg_reg
  infer_instance
instance ireg_inv_persistent records start nib : Persistent (ireg_inv capacity names records start nib) := by
  unfold ireg_inv
  infer_instance

theorem ireg_inv_reg records start nib :
    iprop(⊢ ireg_inv capacity names records start nib -∗ ireg_reg capacity names records start nib) := by
  unfold ireg_inv ireg_reg
  iintro ⟨Hi, Hb, Ht⟩
  iframe Hi Ht
  iapply FsBytesInvariant.any_row (byteCapacity capacity) names.filesystem $$ Hb

theorem ireg_inv_of records start nib :
    iprop(⊢ ireg_reg capacity names records start nib -∗
      FsBlockGhost.exc_sealed capacity.blocks names.filesystem.exceptions -∗
      ireg_inv capacity names records start nib) := by
  unfold ireg_reg ireg_inv
  iintro ⟨Hi, Hb, Ht⟩ Hs
  iframe Hi Ht
  unfold FsBytesInvariant.any byteCapacity
  iframe

theorem ireg_inv_bytes records start nib :
    iprop(⊢ ireg_inv capacity names records start nib -∗
      FsBytesInvariant.any (byteCapacity capacity) names.filesystem) := by
  unfold ireg_inv
  iintro ⟨_, Hb, _⟩
  iexact Hb

theorem ireg_inv_ftop records start nib :
    iprop(⊢ ireg_inv capacity names records start nib -∗ topInvariant capacity names) := by
  unfold ireg_inv
  iintro ⟨_, _, Ht⟩
  iexact Ht

/-- The final native invariant-allocation step consumes the provided full body;
all client and byte/top resource preparation remains with the caller. -/
theorem allocate records start nib (E : CoPset) (frame : IProp GF) :
    iprop(⊢ body capacity names records start nib -∗
      FsBytesInvariant.row (byteCapacity capacity) names.filesystem -∗ topInvariant capacity names -∗
      frame ={E}=∗ ireg_reg capacity names records start nib ∗ frame) := by
  iintro Hb Hbytes Htop Hframe
  imod inv_alloc iregN E (body capacity names records start nib) $$ [Hb] with Hi
  · iintro !>
    iexact Hb
  · imodintro
    unfold ireg_reg
    iframe

theorem actual : Spec capacity :=
  ⟨fun names => ireg_inv_reg capacity names, fun names => ireg_inv_of capacity names,
    fun names => ireg_inv_bytes capacity names, fun names => ireg_inv_ftop capacity names,
    fun names => allocate capacity names⟩

end MachCSL.Logic.IcacheRegionInvariant
