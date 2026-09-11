import Xv6.Fs.DurableNodeDefs

namespace Xv6.Fs.DurableNode

/-- The five source inode_repr fields; no validity/size assumption is implicit. -/
structure Repr (n : Node) : Prop where
  record : n.record.WellFormed
  entryLength : n.entries.length = 256
  indirectZero : n.indirect = 0 → n.entries = List.replicate 256 0
  domain : ∀ k, k < 268 → (n.blocks[k]?.isSome ↔ n.address k ≠ 0)
  top : ∀ k, 268 ≤ k → n.blocks[k]? = none

/-- All sixteen source inode_local clauses, including the orphan guards. -/
structure Local (inum : Int) (n : Node) : Prop where
  record : n.record.WellFormed
  entryLength : n.entries.length = 256
  indirectZero : n.indirect = 0 → n.entries = List.replicate 256 0
  domain : ∀ k, k < 268 → (n.blocks[k]?.isSome ↔ n.address k ≠ 0)
  top : ∀ k, 268 ≤ k → n.blocks[k]? = none
  blockLength : ∀ (k : Nat) (bytes : List (BitVec 8)), n.blocks[k]? = some bytes → bytes.length = 1024
  type : n.typeZ = 0 ∨ n.typeZ = 1 ∨ n.typeZ = 2 ∨ n.typeZ = 3
  size : 0 ≤ n.sizeZ ∧ n.sizeZ ≤ 268 * 1024
  covers : ∀ (k : Nat), k < 268 → (k : Int) * 1024 < n.sizeZ → n.address k ≠ 0
  free : n.typeZ = 0 → n.nlink = 0
  nlink : n.record.nlinkZ ≤ 32767
  dirSize : n.isDir = true → 16 ∣ n.sizeZ
  dirUnique : n.isDir = true → DirNamesUnique n.data n.nrec
  dirDot : n.isDir = true → n.nlink ≠ 0 → n.dirEntries[dotName]? = some inum
  dirDotdot : n.isDir = true → n.nlink ≠ 0 → n.dirEntries[dotdotName]?.isSome
  bareFree : n.typeZ = 0 → n.Bare

/-- Source DirView.dir_ok; total reads and free-entry garbage are retained. -/
def DirOK (nib : Nat) (n : Node) : Prop :=
  n.typeZ = 1 → DirInumsOK n.data n.nrec nib

def DirDotsOnly (n : Node) : Prop :=
  ∀ k, k < n.nrec → DirLive n.data k →
    dirBname n.data k = dotName ∨ dirBname n.data k = dotdotName

def DirOrphanClean (n : Node) : Prop := n.typeZ = 1 → n.nlink = 0 → DirDotsOnly n

/-- The source's three region-local clauses, separate from inode_local. -/
def DirLocal (inum : Int) (nib : Nat) (n : Node) : Prop :=
  DirOK nib n ∧ DirDotsIx inum n.record n.data ∧ DirOrphanClean n

end Xv6.Fs.DurableNode
