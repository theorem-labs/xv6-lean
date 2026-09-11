import MachCSL.Logic.FsDurInodeReadSlotProofs
import MachCSL.Logic.FsDurReadProofs

namespace MachCSL.Logic.FsDurInodeRead
open Iris Iris.Std Iris.BI Xv6.Fs DurableNode DurableState
variable {GF : BundledGFunctors} (capacity : Disk.Capacity GF)

theorem snap_read_blks g gl gt disk (node : Node) (full : FsDurRead.BlocksFull disk) :
    FsDurBytes.snapAuth capacity g disk ∗ dataLeg (FsView.snapGamma capacity g gl gt) node ⊢
      ⌜∀ k bytes, node.blocks[k]? = some bytes → disk[node.address k]? = some bytes⌝ := by
  iintro ⟨Ha, Hd⟩
  iapply pure_forall.mpr
  iintro %k
  iapply pure_forall.mpr
  iintro %bytes
  iapply pure_imp.mpr
  iintro %found
  unfold dataLeg
  ihave Hb := BigSepM.bigSepM_lookup (M := FsState.SlotMap) found $$ Hd
  iapply FsDurRead.snap_blk_read_full capacity g gl gt disk (node.address k) bytes full $$ [$Ha $Hb]

theorem snap_read_ind g gl gt disk (node : Node) (full : FsDurRead.BlocksFull disk) :
    FsDurBytes.snapAuth capacity g disk ∗ FsState.indOwned (FsView.snapGamma capacity g gl gt) node ⊢
      ⌜node.indirect ≠ 0 → disk[node.indirect]? = some (indirectBytes node.entries)⌝ := by
  iintro ⟨Ha, Hi⟩
  iapply pure_imp.mpr
  iintro %nonzero
  unfold FsState.indOwned FsState.indOwnedQ
  rw [if_neg nonzero]
  iapply FsDurRead.snap_blk_read capacity g gl gt disk (.own 1) node.indirect (indirectBytes node.entries) full $$ [$Ha $Hi]

theorem snap_read_pool g gl gt disk nb used (full : FsDurRead.BlocksFull disk) :
    FsDurBytes.snapAuth capacity g disk ∗ FsState.freePool (FsView.snapGamma capacity g gl gt) nb used ⊢
      ⌜∀ b, 0 ≤ b ∧ b < nb → b ∉ used → (disk[b]?).isSome⌝ := by
  iintro ⟨Ha, Hp⟩
  iapply pure_forall.mpr
  iintro %b
  iapply pure_imp.mpr
  iintro %bound
  iapply pure_imp.mpr
  iintro %unused
  ihave Hp := FsState.freePool_lookup (FsView.snapGamma capacity g gl gt) nb used b bound $$ Hp
  rw [FsState.poolElt_free (FsView.snapGamma capacity g gl gt) used b unused]
  icases Hp with ⟨%bytes, Hb⟩
  ihave Hb := (BIBase.BiEntails.of_eq (FsView.blockOwned_one (FsView.snapGamma capacity g gl gt) b bytes)).mp $$ Hb
  iapply FsDurRead.snap_blk_dom capacity g gl gt disk (.own 1) b bytes full $$ [$Ha $Hb]

theorem snap_read_inode g gl gt disk sb i (node : Node) (full : FsDurRead.BlocksFull disk)
    (bound : 0 ≤ i ∧ i < 2 ^ 32) (hlocal : DurableNode.Local i node) :
    FsDurBytes.snapAuth capacity g disk ∗ FsState.inodePhi (FsView.snapGamma capacity g gl gt) sb i node ⊢
      ⌜Snapshot.InodeRead sb disk i node⌝ := by
  unfold FsState.inodePhi
  iintro ⟨Ha, Hr, Hd⟩
  ihave %slots := inode_dat_slot_inj (FsView.snapGamma capacity g gl gt)
    (FsView.snapGamma_excl capacity g gl gt) i node hlocal $$ Hd
  unfold FsState.inodeDat FsState.inodeDatQ
  icases Hd with ⟨Hd, Hi⟩
  have readBlocks := snap_read_blks capacity g gl gt disk node full
  simp only [dataLeg, FsView.blockOwned_one] at readBlocks
  ihave %blocks := readBlocks $$ [$Ha $Hd]
  have readIndirect := snap_read_ind capacity g gl gt disk node full
  rw [FsState.indOwned_one] at readIndirect
  ihave %indirect := readIndirect $$ [$Ha $Hi]
  rw [← FsState.recOwnedAt_sb (FsView.snapGamma capacity g gl gt) sb i node.record bound]
  unfold FsState.recOwnedAt FsState.recOwnedAtQ
  have len := dinodeBytes_length node.record hlocal.record
  have modbound : 0 ≤ i % 16 ∧ i % 16 < 16 := ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  ihave %record := FsDurRead.snap_run_read capacity g gl gt disk (.own 1)
    (sb.inodestart + i / 16) (64 * (i % 16)) (dinodeBytes node.record)
    full (by omega) (by omega) (by omega) $$ [$Ha $Hr]
  ipureintro
  obtain ⟨bytes, get, _, pre, post, split, offset⟩ := record
  exact ⟨⟨bytes, get, pre, post, split, offset⟩, blocks, indirect, slots⟩

theorem snap_read_inodes g gl gt disk sb nodes (full : FsDurRead.BlocksFull disk)
    (bounds : ∀ (i : Int) node, nodes[i]? = some node → 0 ≤ i ∧ i < 2 ^ 32)
    (locals : ∀ (i : Int) node, nodes[i]? = some node → DurableNode.Local i node) :
    FsDurBytes.snapAuth capacity g disk ∗ inodeLeg (FsView.snapGamma capacity g gl gt) sb nodes ⊢
      ⌜∀ i node, nodes[i]? = some node → Snapshot.InodeRead sb disk i node⌝ := by
  iintro ⟨Ha, Hi⟩
  iapply pure_forall.mpr
  iintro %i
  iapply pure_forall.mpr
  iintro %node
  iapply pure_imp.mpr
  iintro %found
  unfold inodeLeg
  ihave Hnode := BigSepM.bigSepM_lookup (M := FsState.InodeMap) found $$ Hi
  iapply snap_read_inode capacity g gl gt disk sb i node full (bounds i node found) (locals i node found) $$ [$Ha $Hnode]

theorem readSpec : ReadSpec capacity where
  inode := snap_read_inode capacity
  inodes := snap_read_inodes capacity

end MachCSL.Logic.FsDurInodeRead
