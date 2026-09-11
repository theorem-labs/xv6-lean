import Xv6.Fs.DurableStateDefs

/-! Exact decoded image node/state from FsCfgBoot and FsDurImg. The region
map includes every rounded inode, including free records. -/
namespace Xv6.Fs.DurableImageNode
open DurableNode

def imageNode (image : Blocks) (sb : Superblock) (inum : Int) : Node :=
  let dn := dinode image sb inum
  DurableNode.nodeOf dn ((indirectEntries image dn).map (BitVec.ofInt 32)) (dataOf image dn)

/-- Ascending unique keys. Lookup characterizes the source finite-set
list_to_map independently of its concrete enumeration order. -/
def nodesUpto (image : Blocks) (sb : Superblock) : Nat → DurableState.InodeMap
  | 0 => ∅
  | count + 1 => (nodesUpto image sb count).insert (count : Int) (imageNode image sb count)

def imageNodes (image : Blocks) (sb : Superblock) (nib : Nat) : DurableState.InodeMap :=
  nodesUpto image sb (16 * nib)

def imageState (image : Blocks) (sb : Superblock) (nib : Nat) : DurableState.State :=
  ⟨sb, image 1, imageNodes image sb nib, bitmapSet 1024 (image sb.bmapstart)⟩

end Xv6.Fs.DurableImageNode
