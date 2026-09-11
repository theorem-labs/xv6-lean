import Xv6.Fs.DurableNodeSpec
import Xv6.Fs.BitmapDefs

/-! FsState.fs_state_rec/fs_geom and FsDurSnap.snap_meta. The finite state
carrier imposes no hidden geometry, completeness or local validity condition. -/
namespace Xv6.Fs.DurableState

abbrev InodeMap := Std.ExtTreeMap Int DurableNode.Node
abbrev BlockMap := Std.ExtTreeMap Int (List (BitVec 8))

structure State where
  superblock : Superblock
  superblockBytes : List (BitVec 8)
  inodes : InodeMap
  used : BlockSet

def State.nib (s : State) : Nat := (s.superblock.ninodes / 16 + 1).toNat

structure Geometry (s : State) : Prop where
  superblock : SuperblockOK s.superblock
  region : ∀ (i : Int) (n : DurableNode.Node), s.inodes[i]? = some n →
    0 ≤ i ∧ i / 16 < s.superblock.bmapstart - s.superblock.inodestart
  domain : ∀ i : Int, 0 ≤ i ∧ i < 16 * (s.superblock.ninodes / 16 + 1) →
    s.inodes[i]?.isSome
  directory : ∀ (i : Int) (n : DurableNode.Node), s.inodes[i]? = some n →
    DurableNode.DirLocal i s.nib n

def Local (s : State) : Prop :=
  ∀ (i : Int) (n : DurableNode.Node), s.inodes[i]? = some n → DurableNode.Local i n

def Metadata (s : State) (b : Int) : Prop :=
  b = 1 ∨ b = s.superblock.bmapstart ∨
    ∃ i : Int, s.inodes[i]?.isSome ∧ b = s.superblock.inodestart + i / 16

/-- Exact split-shaped source rec_in_blk; signed offsets remain explicit. -/
def RecordInBlock (bytes : List (BitVec 8)) (offset : Int) (record : Dinode) : Prop :=
  ∃ pre post, bytes = pre ++ dinodeBytes record ++ post ∧ (pre.length : Int) = offset

end Xv6.Fs.DurableState
