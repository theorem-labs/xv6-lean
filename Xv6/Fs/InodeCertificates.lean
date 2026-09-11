import Xv6.Fs.DiskReaders
import Xv6.Fs.InodeImage

/-! Rounded inode-region checks over the pinned fs.img. Full W3 is separate. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
namespace Xv6.Fs.Image

theorem region_nlink_checked : regionNlink blockView superblock 13 = true := by
  simp only [regionNlink, blockView, dinode_blocks, diskDinode, Dinode.typeZ, Dinode.nlinkZ]
  decide

theorem region_bare_checked : regionBare blockView superblock 13 = true := by
  simp only [regionBare, blockView, dinode_blocks, diskDinode, Dinode.typeZ,
    recordBare, Dinode.sizeZ]
  decide

theorem region_valid_checked : regionValid blockView superblock 13 = true :=
  (regionValid_iff blockView superblock 13).mpr ⟨region_free_checked, region_nlink_checked⟩

end Xv6.Fs.Image
