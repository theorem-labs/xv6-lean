import Xv6.Fs.DirectoryCertificateProofs
import Xv6.Generated.DirectoryInputs
import Xv6.Generated.InodeW3Leaf01
import Xv6.Fs.InodeImage

/-! Checked root-directory input; literal bytes retain all free entries and padding. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Xv6.Fs.Image
open Xv6.Generated.InodeW3 Xv6.Generated.Directory

def rootDirectoryData : FileData := fun k =>
  if k = 0 then rootBytes else List.replicate 1024 0

theorem root_directory_block : blockView 47 = rootBytes := by decide

theorem root_directory_data : dataOf blockView record01 = rootDirectoryData := by
  funext k
  rw [dataOf_one_block blockView record01 47 (by rfl) (by decide) k]
  simp only [rootDirectoryData, root_directory_block]

theorem directory_inode_list : directoryInodes blockView superblock = [1] := by
  simp only [directoryInodes, Dinode.typeZ, blockView, dinode_type_blocks]
  decide

end Xv6.Fs.Image
