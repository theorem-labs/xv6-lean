import Xv6.Fs.TreeDefs

namespace Xv6.Fs

def fileData (image : Blocks) (sb : Superblock) (i : Int) : FileData :=
  dataOf image (dinode image sb i)

def nodeAt (image : Blocks) (sb : Superblock) (i : Int) : Option FsNode :=
  let dn := dinode image sb i
  if dn.typeZ == 0 then none else some (nodeOf dn (dataOf image dn))

def nodesUpto (image : Blocks) (sb : Superblock) : Nat → Std.ExtTreeMap Int FsNode
  | 0 => ∅
  | n + 1 => match nodeAt image sb (n : Int) with
    | some node => (nodesUpto image sb n).insert (n : Int) node
    | none => nodesUpto image sb n

def treeOfDisk (image : Blocks) (sb : Superblock) : FsTree :=
  ⟨nodesUpto image sb sb.ninodes.toNat, 1⟩

end Xv6.Fs
