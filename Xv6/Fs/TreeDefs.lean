import Xv6.Fs.DirentDefs
import Xv6.Fs.InodeValidityDefs

namespace Xv6.Fs

inductive FsNode where
  | file (bytes : List (BitVec 8))
  | directory (entries : NameMap)

structure FsTree where
  nodes : Std.ExtTreeMap Int FsNode
  root : Int

def fileBytes (data : FileData) (n : Nat) : List (BitVec 8) :=
  (List.range n).map (fileByte data)

/-- Every non-directory type uses its full declared bytes, including malformed devices. -/
def nodeOf (dn : Dinode) (data : FileData) : FsNode :=
  if dn.typeZ = 1 then .directory (dirView data (dirNrec dn.sizeZ))
  else .file (fileBytes data dn.size.toNat)

def treeEnt (tree : FsTree) (i : Int) (name : FName) : Option Int :=
  match tree.nodes[i]? with
  | some (.directory entries) => entries[name]?
  | _ => none

def pathStep (tree : FsTree) (i : Option Int) (name : FName) : Option Int :=
  match i with
  | some z => treeEnt tree z name
  | none => none

def pathAt (tree : FsTree) (i : Int) (path : List FName) : Option Int :=
  path.foldl (pathStep tree) (some i)

def pathChain (tree : FsTree) (i : Int) : List FName → List Int
  | [] => [i]
  | name :: rest => i :: (match treeEnt tree i name with
    | some j => pathChain tree j rest
    | none => [])

end Xv6.Fs
