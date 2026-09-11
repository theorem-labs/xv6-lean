import Xv6.Fs.SnapshotImageBytesProofs
import Xv6.Fs.SnapshotHomeProofs
import Xv6.Fs.DurableBlocksProofs

/-! Source `FsDurImg` §11c and the ownership/coverage helpers of §11d.
The source W3/W4/W5 checks justify the image specialization; the general
durable state and arbitrary disk carriers remain unchanged. -/
namespace Xv6.Fs.SnapshotImage
open DurableNode DurableImageNode

theorem image_owned_block (image : Blocks) (sb : Superblock) (i b : Int)
    (valid : fsimgValid image sb = true) (bound : 0 ≤ i ∧ i < sb.ninodes)
    (live : (dinode image sb i).typeZ ≠ 0) (owned : (imageNode image sb i).Owns b) :
    b ∈ inodeBlocks image (dinode image sb i) ∧ dataStart sb ≤ b ∧ b < sb.size := by
  have ok := fsimgValid_inode image sb i valid bound live
  obtain ⟨k, hk, address, nonzero⟩ := image_node_owns_slot image sb i b owned
  have member : b ∈ inodeEntries image (dinode image sb i) :=
    (inodeEntries_member image _ b).mpr ⟨k, hk, address, nonzero⟩
  rw [inodeEntries_eq_blocks image sb _ (fsimgValid_superblock image sb valid) ok] at member
  exact ⟨member, inodeBlocks_range image sb _ ok b member⟩

theorem image_used_of_blocks (image : Blocks) (sb : Superblock) (b : Int)
    (valid : fsimgValid image sb = true) (bound : 0 ≤ b ∧ b < sb.size)
    (used : b < dataStart sb ∨ b ∈ usedBlocks image sb) :
    b ∈ bitmapSet 1024 (image sb.bmapstart) := by
  have geometry := fsimgValid_superblock image sb valid
  obtain ⟨set, collected, _, bitmap⟩ := fsimgValid_used image sb valid
  apply (bitmapSet_mem 1024 _ b).mpr
  refine ⟨⟨bound.1, ?_⟩, (bitmapValid_spec image sb set bitmap b bound).mpr ?_⟩
  · have := geometry.oneBitmap
    omega
  · exact used.imp_right ((usedSet_mem image sb set collected b).mpr)

/-- W4's exact distinct-inode consequence for the source ordered block lists. -/
theorem inodeBlocks_disjoint (image : Blocks) (sb : Superblock) (i j : Int)
    (unique : (usedBlocks image sb).Nodup)
    (left : 0 ≤ i ∧ i < sb.ninodes) (right : 0 ≤ j ∧ j < sb.ninodes)
    (different : i ≠ j) (liveI : (dinode image sb i).typeZ ≠ 0)
    (liveJ : (dinode image sb j).typeZ ≠ 0) (b : Int)
    (inI : b ∈ inodeBlocks image (dinode image sb i))
    (inJ : b ∈ inodeBlocks image (dinode image sb j)) : False := by
  apply nodup_flatten_cross _ i.toNat j.toNat _ _ unique _ _ (by omega) b inI inJ
  · rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Int.toNat_of_nonneg left.1, beq_eq_false_iff_ne.mpr liveI,
      Bool.false_eq_true, ↓reduceIte]
  · rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Int.toNat_of_nonneg right.1, beq_eq_false_iff_ne.mpr liveJ,
      Bool.false_eq_true, ↓reduceIte]

/-- The rounded region includes free records; the bare check makes their
ownership empty instead of removing them from the node map. -/
theorem image_owns_live (h : BootImageWF disk ndisk sb nib cov) (i b : Int)
    (region : 0 ≤ i ∧ i < 16 * (nib : Int))
    (owned : (imageNode (blocks disk) sb i).Owns b) :
    (0 ≤ i ∧ i < sb.ninodes) ∧ (dinode (blocks disk) sb i).typeZ ≠ 0 := by
  have live : (dinode (blocks disk) sb i).typeZ ≠ 0 := by
    intro free
    have bare := imageNode_bare (blocks disk) sb nib i h.bare
      (regionValid_nlink _ _ _ h.region) region free
    exact bare_no_owns bare b owned
  refine ⟨⟨region.1, ?_⟩, live⟩
  by_cases inside : i < sb.ninodes
  · exact inside
  · exact False.elim (live (regionFree_spec (blocks disk) sb nib i
      (regionValid_free _ _ _ h.region) region.1 (by omega) region.2))

theorem image_owned_home (h : BootImageWF disk ndisk sb nib cov) (i b : Int)
    (region : 0 ≤ i ∧ i < 16 * (nib : Int))
    (owned : (imageNode (blocks disk) sb i).Owns b) :
    b ∈ SnapshotHome.homeSet cov sb.logstart ∧ b ∈ usedBlocks (blocks disk) sb ∧
      dataStart sb ≤ b ∧ b < sb.size := by
  obtain ⟨bound, live⟩ := image_owns_live h i b region owned
  obtain ⟨member, range⟩ := image_owned_block (blocks disk) sb i b h.image bound live owned
  exact ⟨SnapshotHome.boot_home_data h b range,
    usedBlocks_inode (blocks disk) sb i b bound live member, range⟩

theorem image_metadata_below (h : BootImageWF disk ndisk sb nib cov) (b : Int)
    (metadata : DurableState.Metadata (imageState (blocks disk) sb nib) b) :
    1 ≤ b ∧ b < dataStart sb := by
  have geometry := bootImage_superblock h
  have bounds := superblock_metadata sb geometry
  change b = 1 ∨ b = sb.bmapstart ∨
    ∃ i : Int, (imageNodes (blocks disk) sb nib)[i]?.isSome ∧ b = sb.inodestart + i / 16 at metadata
  rcases metadata with rfl | rfl | ⟨i, present, rfl⟩
  · omega
  · unfold dataStart at *
    omega
  · rw [imageNodes_lookup] at present
    split at present
    · rename_i region
      have width := h.rounded
      have bitmap := geometry.bmapstart
      unfold dataStart
      constructor <;> omega
    · contradiction

theorem image_owned_used (h : BootImageWF disk ndisk sb nib cov) (i b : Int)
    (region : 0 ≤ i ∧ i < 16 * (nib : Int))
    (owned : (imageNode (blocks disk) sb i).Owns b) :
    b ∈ (imageState (blocks disk) sb nib).used ∧
      ¬DurableState.Metadata (imageState (blocks disk) sb nib) b := by
  obtain ⟨_, used, range⟩ := image_owned_home h i b region owned
  have positive := dataStart_positive sb (bootImage_superblock h)
  refine ⟨image_used_of_blocks (blocks disk) sb b h.image ⟨by omega, range.2⟩ (Or.inr used), ?_⟩
  intro metadata
  have := image_metadata_below h b metadata
  omega

theorem image_owned_disjoint (h : BootImageWF disk ndisk sb nib cov) (i j b : Int)
    (left : 0 ≤ i ∧ i < 16 * (nib : Int)) (right : 0 ≤ j ∧ j < 16 * (nib : Int))
    (ownI : (imageNode (blocks disk) sb i).Owns b)
    (ownJ : (imageNode (blocks disk) sb j).Owns b) : i = j := by
  by_cases equal : i = j
  · exact equal
  · obtain ⟨ri, li⟩ := image_owns_live h i b left ownI
    obtain ⟨rj, lj⟩ := image_owns_live h j b right ownJ
    have bi := (image_owned_block (blocks disk) sb i b h.image ri li ownI).1
    have bj := (image_owned_block (blocks disk) sb j b h.image rj lj ownJ).1
    obtain ⟨_, _, unique, _⟩ := fsimgValid_used (blocks disk) sb h.image
    exact False.elim (inodeBlocks_disjoint (blocks disk) sb i j unique ri rj equal li lj b bi bj)

theorem image_slot_injective (h : BootImageWF disk ndisk sb nib cov) (i : Int)
    (region : 0 ≤ i ∧ i < 16 * (nib : Int)) : (imageNode (blocks disk) sb i).SlotInjective := by
  by_cases free : (dinode (blocks disk) sb i).typeZ = 0
  · exact bare_slot_injective (imageNode_bare (blocks disk) sb nib i h.bare
      (regionValid_nlink _ _ _ h.region) region free)
  · have bound : 0 ≤ i ∧ i < sb.ninodes := by
      refine ⟨region.1, ?_⟩
      by_cases inside : i < sb.ninodes
      · exact inside
      · exact False.elim (free (regionFree_spec (blocks disk) sb nib i
          (regionValid_free _ _ _ h.region) region.1 (by omega) region.2))
    obtain ⟨_, _, unique, _⟩ := fsimgValid_used (blocks disk) sb h.image
    apply image_node_slot_injective
    exact usedBlocks_slot_injective (blocks disk) sb i (bootImage_superblock h)
      ((fsimgValid_iff _ _).mp h.image).inodes unique bound free

/-- W5 excludes every metadata block, including block zero, from the free
pool. Its remaining members therefore lie in actual covered home data. -/
theorem image_pool_home (h : BootImageWF disk ndisk sb nib cov) (b : Int)
    (bound : 0 ≤ b ∧ b < sb.size) (free : b ∉ (imageState (blocks disk) sb nib).used) :
    b ∈ SnapshotHome.homeSet cov sb.logstart := by
  obtain ⟨used, _, _, bitmap⟩ := fsimgValid_used (blocks disk) sb h.image
  have range := bitmapSet_free (blocks disk) sb used 1024 bitmap
    (bootImage_superblock h).oneBitmap b bound free
  exact SnapshotHome.boot_home_data h b ⟨range.1, bound.2⟩

end Xv6.Fs.SnapshotImage
