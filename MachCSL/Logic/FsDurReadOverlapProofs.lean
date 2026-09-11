import MachCSL.Logic.FsDurReadSpec
import MachCSL.Logic.FsStateBitmapProofs
import MachCSL.Logic.FsStateInodeDefs

namespace MachCSL.Logic.FsDurRead
open Iris Iris.Std Iris.BI Iris.CMRA Xv6.Fs DurableState
variable {GF : BundledGFunctors} (view : FsView.View GF)

theorem byte_range_q_overlap (exclusive : FsView.PhiExcl view) (dq1 dq2 : DFrac)
    b off1 off2 bytes1 bytes2 (k1 k2 : Nat) (invalid : ¬✓ (dq1 • dq2))
    (bound1 : k1 < bytes1.length) (bound2 : k2 < bytes2.length)
    (same : off1 + (k1 : Int) = off2 + (k2 : Int)) :
    FsView.byteRangeQ view dq1 b off1 bytes1 ∗ FsView.byteRangeQ view dq2 b off2 bytes2 ⊢ ⌜False⌝ := by
  unfold FsView.byteRangeQ
  iintro ⟨Hl, Hr⟩
  ihave H1 := BigSepL.bigSepL_lookup (List.getElem?_eq_getElem bound1) $$ Hl
  ihave H2 := BigSepL.bigSepL_lookup (List.getElem?_eq_getElem bound2) $$ Hr
  have address : b * 1024 + off1 + (k1 : Int) = b * 1024 + off2 + (k2 : Int) := by omega
  rw [address]
  ihave %valid := exclusive _ _ _ dq1 dq2 $$ [$H1 $H2]
  ipureintro
  exact invalid valid

theorem blk_run_overlap (exclusive : FsView.PhiExcl view) (dq1 dq2 : DFrac)
    b off block bytes (invalid : ¬✓ (dq1 • dq2))
    (nonneg : 0 ≤ off) (fits : off + (bytes.length : Int) ≤ 1024) (nonempty : 0 < bytes.length) :
    FsView.blockOwnedQ view dq1 b block ∗ FsView.byteRangeQ view dq2 b off bytes ⊢ ⌜False⌝ := by
  unfold FsView.blockOwnedQ
  iintro ⟨⟨%length, Hb⟩, Hr⟩
  iapply byte_range_q_overlap view exclusive dq1 dq2 b 0 off block bytes off.toNat 0 invalid
    (by omega) nonempty (by omega) $$ [$Hb $Hr]

theorem free_pool_used_run (exclusive : FsView.PhiExcl view) nb used b off bytes
    (bound : 0 ≤ b ∧ b < nb) (nonneg : 0 ≤ off)
    (fits : off + (bytes.length : Int) ≤ 1024) (nonempty : 0 < bytes.length) :
    FsState.freePool view nb used ∗ FsView.byteRange view b off bytes ⊢ ⌜b ∈ used⌝ := by
  by_cases found : b ∈ used
  · iintro _; ipureintro; exact found
  · iintro ⟨Hpool, Hr⟩
    ihave Hpool := FsState.freePool_lookup view nb used b bound $$ Hpool
    rw [FsState.poolElt_free view used b found]
    icases Hpool with ⟨%block, Hb⟩
    ihave Hb := (BIBase.BiEntails.of_eq (FsView.blockOwned_one view b block)).mp $$ Hb
    ihave Hr := (BIBase.BiEntails.of_eq (FsView.byteRange_one view b off bytes)).mp $$ Hr
    ihave %impossible := blk_run_overlap view exclusive (.own 1) (.own 1) b off block bytes
      (FsView.dfrac_full_invalid _) nonneg fits nonempty $$ [$Hb $Hr]
    ipureintro
    exact False.elim impossible

theorem inode_phi_dat sb i node :
    FsState.inodePhi view sb i node ⊣⊢
      FsState.recOwned view sb i node.record ∗ FsState.inodeDat view node := .rfl

theorem overlapSpec : OverlapSpec view where
  overlap dq1 dq2 b off1 off2 bytes1 bytes2 k1 k2 exclusive :=
    byte_range_q_overlap view exclusive dq1 dq2 b off1 off2 bytes1 bytes2 k1 k2
  poolUsed nb used b off bytes exclusive := free_pool_used_run view exclusive nb used b off bytes

end MachCSL.Logic.FsDurRead
