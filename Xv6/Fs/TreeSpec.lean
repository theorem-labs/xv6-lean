import Xv6.Fs.TreeDefs

namespace Xv6.Fs

/-- Source FsTree.node_rep; uniqueness constrains representation, not nodeOf. -/
def NodeRep (node : FsNode) (dn : Dinode) (data : FileData) : Prop :=
  match node with
  | .file bytes => dn.typeZ ≠ 0 ∧ dn.typeZ ≠ 1 ∧ bytes = fileBytes data dn.size.toNat
  | .directory entries => dn.typeZ = 1 ∧ DirNamesUnique data (dirNrec dn.sizeZ) ∧
      entries = dirView data (dirNrec dn.sizeZ)

def InumsOK (tree : FsTree) : Prop :=
  ∀ (i : Int) node, tree.nodes[i]? = some node → 0 ≤ i ∧ i < 2 ^ 32

def RootDirectory (tree : FsTree) : Prop :=
  ∃ entries, tree.nodes[tree.root]? = some (.directory entries)

def TreeWellFormed (tree : FsTree) : Prop := InumsOK tree ∧ RootDirectory tree

def ProperPath (path : List FName) : Prop :=
  ∀ name ∈ path, name ≠ dotName ∧ name ≠ dotdotName

def DirectoriesAcyclic (tree : FsTree) : Prop :=
  ∀ i path, path ≠ [] → ProperPath path → pathAt tree i path ≠ some i

end Xv6.Fs
