import Xv6.Fs.IcacheRegionImageDefs
import Xv6.Fs.SnapshotImage
import Xv6.Fs.SnapshotRegionProofs
import MachCSL.Logic.IcacheRegionBootLink

set_option maxRecDepth 2048

namespace Xv6.Fs.Image.IcacheRegion
open Iris Iris.BI MachCSL.Logic

attribute [local irreducible] state DurableImageNode.imageState SnapshotHome.homeMap

theorem inodeBlocks_length : inodeBlocks.length = 13 := by simp only [inodeBlocks, List.length_map, List.length_range]

theorem inodeBlocks_at (bi : Nat) (bound : bi < 13) :
    inodeBlocks[bi]?.getD [] = blockView (superblock.inodestart + (bi : Int)) := by
  simp only [inodeBlocks, List.getElem?_map, List.getElem?_range bound, Option.map_some, Option.getD_some]

theorem inodeBlocks_full (bytes : List (BitVec 8)) (member : bytes ∈ inodeBlocks) : bytes.length = 1024 := by
  obtain ⟨bi, _, rfl⟩ := List.mem_map.mp member
  exact blocks_full _

theorem imageNames_start (names : IcacheRegionSlot.Names) : (imageNames names).epoch.inodeStart = 33 := rfl
theorem imageNames_observations (names : IcacheRegionSlot.Names) :
    (imageNames names).epoch.observation = names.epoch.observation := rfl
theorem imageNames_logEpoch (names : IcacheRegionSlot.Names) :
    (imageNames names).epoch.logEpoch = names.epoch.logEpoch := rfl
theorem imageNames_logged (names : IcacheRegionSlot.Names) :
    (imageNames names).epoch.logged = names.epoch.logged := rfl

theorem imageNames_iblk (names : IcacheRegionSlot.Names) (inum : BitVec 32) :
    IcacheEpoch.iblkOf (imageNames names).epoch inum.toNat = inodeBlock inum superblock.inodestart := rfl

/-- All six universal decoder premises follow from the existing full snapshot
proof, including every inode in the padded 208-inode region. -/
theorem decoded_premises (dss : List (List Dinode)) (decoded : FsInodeRegion.Decoded inodeBlocks dss) :
    InodeRegionImage.Premises dss inodeBlocks.length counts imageRecords := by
  have valid : Snapshot.OK state (SnapshotHome.homeMap blockView initialCoverage superblock.logstart) := by
    unfold state
    exact snapshot_ok
  have state_sb : state.superblock = superblock := by
    unfold state DurableImageNode.imageState
    rfl
  have width : (13 : Int) = state.superblock.ninodes / 16 + 1 := by
    rw [state_sb]
    rfl
  have length : dss.length = 13 := decoded.1.trans inodeBlocks_length
  have encoded (bi : Nat) (bound : bi < 13) :
      blockView (state.superblock.inodestart + (bi : Int)) = inodeBlockBytes (dss[bi]?.getD []) := by
    rw [state_sb]
    rw [← inodeBlocks_at bi bound]
    exact decoded.2.2 bi (by rw [inodeBlocks_length]; exact bound)
  have bytes : Snapshot.Bytes state (SnapshotHome.restrict blockView
      (SnapshotHome.homeSet initialCoverage superblock.logstart)) := by
    simpa only [SnapshotHome.homeMap] using valid.1
  rw [inodeBlocks_length]
  exact SnapshotConfig.snap_ireg_premises state blockView
    (SnapshotHome.homeSet initialCoverage superblock.logstart) dss 13 blocks_full bytes valid.2
    width (by decide) length decoded.2.1 encoded

/-- Actual artifact body construction. Native client columns and existing
empty registry authority remain supplied resources, not consequences of pure validity. -/
theorem bootstrap_body (names : IcacheRegionSlot.Names)
    (view : FsView.View IcacheEscrowTokens.registry) (frame : IProp IcacheEscrowTokens.registry) :
    iprop(FsInodeRegion.regionBytes view superblock.inodestart inodeBlocks ∗
      IcacheRegionBoot.clients IcacheRegionSlot.nativeCapacity (imageNames names) view 13 counts imageRecords ∗
      IcacheEscrowTokens.reg_auth IcacheEscrowTokens.registryCapacity names.registry ∅ ∗ frame ⊢ |==> ∃ records dss,
      ⌜FsInodeRegion.Decoded inodeBlocks dss ∧ InodeRegionImage.Premises dss 13 counts imageRecords⌝ ∗
      IcacheRegionBoot.body IcacheRegionSlot.nativeCapacity (imageNames names) view records superblock.inodestart 13 ∗
      IcacheRegionBoot.outside IcacheRegionSlot.nativeCapacity records dss 13 ∗ frame) := by
  have boot := IcacheRegionBoot.bootstrap_body IcacheRegionSlot.nativeCapacity (imageNames names) view
    superblock.inodestart inodeBlocks counts imageRecords frame inodeBlocks_full
    (by rw [inodeBlocks_length]; decide) decoded_premises
  simpa only [inodeBlocks_length, IcacheRegionSlot.nativeCapacity, imageNames] using boot

end Xv6.Fs.Image.IcacheRegion
