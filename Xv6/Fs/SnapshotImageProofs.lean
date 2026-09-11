import Xv6.Fs.SnapshotImageOwnershipProofs
import Xv6.Fs.SnapshotProofs
import Xv6.Fs.BitmapEncodingProofs
import Xv6.Fs.LinkImageProofs

/-! Exact initial-image snapshot assembly, source `FsDurImg.img_snap_ok`.
Only the existing fifteen-conjunct boot-image hypothesis is required. -/
namespace Xv6.Fs.SnapshotImage
open DurableNode DurableImageNode DurableState SnapshotHome LinkFamily

set_option maxRecDepth 2048 in
theorem image_bytes (h : BootImageWF disk ndisk sb nib cov) :
    Snapshot.Bytes (imageState (blocks disk) sb nib) (homeMap (blocks disk) cov sb.logstart) where
  blockSize := by
    intro b bytes present
    obtain ⟨_, rfl⟩ := (restrict_lookup_some _ _ b bytes).mp present
    exact blocks_length disk b
  superblock := (restrict_lookup_some _ _ 1 _).mpr ⟨boot_home_superblock h, rfl⟩
  parse := h.parsed
  bitmap := by
    change (homeMap (blocks disk) cov sb.logstart)[sb.bmapstart]? =
      some (BitmapEncoding.bitmapBytes 1024 (bitmapSet 1024 (blocks disk sb.bmapstart)))
    rw [BitmapEncoding.bitmapBytes_roundtrip 1024 _ (blocks_length disk _)]
    apply (restrict_lookup_some _ _ _ _).mpr
    refine ⟨boot_home_region h _ ?_, rfl⟩
    have := bootImage_region_end h
    unfold dataStart
    constructor <;> omega
  pool := by
    intro b bound free
    exact (restrict_domain _ _ b).mpr (image_pool_home h b bound free)
  inum := by
    intro i n found
    obtain ⟨bound, _⟩ := imageNodes_lookup_inv _ _ _ i n found
    have := h.wordBound
    constructor <;> omega
  repr := by
    intro i n found
    obtain ⟨_, rfl⟩ := imageNodes_lookup_inv _ _ _ i n found
    exact imageNode_repr _ _ _
  record := by
    intro i n found
    obtain ⟨bound, rfl⟩ := imageNodes_lookup_inv _ _ _ i n found
    refine ⟨blocks disk (sb.inodestart + i / 16), ?_, ?_⟩
    · apply (restrict_lookup_some _ _ _ _).mpr
      refine ⟨boot_home_region h _ ?_, rfl⟩
      have endpoint := bootImage_region_end h
      change sb.inodestart ≤ sb.inodestart + i / 16 ∧ sb.inodestart + i / 16 < dataStart sb
      unfold dataStart
      constructor <;> omega
    · exact image_record_in_block (blocks disk) sb i (blocks_length disk)
        ⟨bound.1, by have := h.wordBound; omega⟩
  data := by
    intro i n k bytes found held
    obtain ⟨bound, rfl⟩ := imageNodes_lookup_inv _ _ _ i n found
    obtain ⟨value, owned⟩ := image_node_data_at (blocks disk) sb i k bytes held
    exact (restrict_lookup_some _ _ _ _).mpr ⟨(image_owned_home h i _ bound owned).1, value⟩
  indirect := by
    intro i n found nonzero
    obtain ⟨bound, rfl⟩ := imageNodes_lookup_inv _ _ _ i n found
    obtain ⟨value, owned⟩ := image_node_indirect_at (blocks disk) sb i (blocks_length disk) nonzero
    exact (restrict_lookup_some _ _ _ _).mpr ⟨(image_owned_home h i _ bound owned).1, value.symm⟩
  domain := by
    intro i bound
    change 0 ≤ i ∧ i < sb.ninodes at bound
    apply (imageState_all_inodes _ _ _ i).mpr
    have := h.advertised
    exact ⟨bound.1, by omega⟩
  links := ⟨imageChoice (blocks disk) sb, imageValue (blocks disk) sb 1,
    image_elem_ok (blocks disk) sb nib h.image h.region, LinkImage.bootImage_link_valid h⟩
  metadataUsed := by
    intro b metadata
    have range := image_metadata_below h b metadata
    have geometry := superblock_metadata sb (bootImage_superblock h)
    exact image_used_of_blocks (blocks disk) sb b h.image
      ⟨by omega, by omega⟩ (Or.inl range.2)
  ownedUsed := by
    intro i n b found owned
    obtain ⟨bound, rfl⟩ := imageNodes_lookup_inv _ _ _ i n found
    exact image_owned_used h i b bound owned
  disjoint := by
    intro i n j m b foundI foundJ ownI ownJ
    obtain ⟨boundI, rfl⟩ := imageNodes_lookup_inv _ _ _ i n foundI
    obtain ⟨boundJ, rfl⟩ := imageNodes_lookup_inv _ _ _ j m foundJ
    exact image_owned_disjoint h i j b boundI boundJ ownI ownJ
  superblockOK := bootImage_superblock h
  region := (imageState_geometry h).region
  slot := by
    intro i n found
    obtain ⟨bound, rfl⟩ := imageNodes_lookup_inv _ _ _ i n found
    exact image_slot_injective h i bound
  regionDomain := (imageState_geometry h).domain
  directory := (imageState_geometry h).directory
  domainBelow := by
    intro b present
    have bound := homeMap_below (blocks disk) cov ndisk sb.logstart sb h.coverage h.diskBound b present
    exact ⟨by omega, bound.2⟩

/-- The full source theorem: bytes and local-node validity together. -/
theorem image_snap_ok (h : BootImageWF disk ndisk sb nib cov) :
    Snapshot.OK (imageState (blocks disk) sb nib) (homeMap (blocks disk) cov sb.logstart) :=
  ⟨image_bytes h, imageState_local h⟩

theorem image_snap_holds (h : BootImageWF disk ndisk sb nib cov) :
    Snapshot.Holds (homeMap (blocks disk) cov sb.logstart) :=
  ⟨imageState (blocks disk) sb nib, image_snap_ok h⟩

end Xv6.Fs.SnapshotImage
