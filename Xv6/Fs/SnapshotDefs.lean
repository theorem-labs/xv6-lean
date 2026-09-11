import Xv6.Fs.DurableStateDefs
import Xv6.Fs.BitmapEncodingDefs
import Xv6.Fs.LinkFamilyDefs

/-! Exact pure durable snapshot contract, FsDurSnap.v:261–406, 516–546.
Every byte and cross-node clause is retained over the arbitrary state carrier. -/
namespace Xv6.Fs.Snapshot
open DurableState DurableNode LinkFamily MachCSL.Logic.FsLink Iris Iris.CMRA

structure Bytes (state : State) (disk : BlockMap) : Prop where
  blockSize : ∀ (b : Int) bytes, disk[b]? = some bytes → bytes.length = 1024
  superblock : disk[(1 : Int)]? = some state.superblockBytes
  parse : parseSuperblock (fun _ => state.superblockBytes) = some state.superblock
  bitmap : disk[state.superblock.bmapstart]? = some (BitmapEncoding.bitmapBytes 1024 state.used)
  pool : ∀ b : Int, 0 ≤ b ∧ b < state.superblock.size → b ∉ state.used → disk[b]?.isSome
  inum : ∀ (i : Int) (n : Node), state.inodes[i]? = some n → 0 ≤ i ∧ i < 2 ^ 32
  repr : ∀ (i : Int) (n : Node), state.inodes[i]? = some n → DurableNode.Repr n
  record : ∀ (i : Int) (n : Node), state.inodes[i]? = some n →
    ∃ bytes, disk[state.superblock.inodestart + i / 16]? = some bytes ∧
      RecordInBlock bytes (64 * (i % 16)) n.record
  data : ∀ (i : Int) (n : Node) (k : Nat) bytes, state.inodes[i]? = some n →
    n.blocks[k]? = some bytes → disk[n.address k]? = some bytes
  indirect : ∀ (i : Int) (n : Node), state.inodes[i]? = some n → n.indirect ≠ 0 →
    disk[n.indirect]? = some (indirectBytes n.entries)
  domain : ∀ i : Int, 0 ≤ i ∧ i < state.superblock.ninodes → state.inodes[i]?.isSome
  links : ∃ f value, ElemOK state.inodes f ∧ ✓ (elem state.inodes f • tokElem 1 value)
  metadataUsed : ∀ b, Metadata state b → b ∈ state.used
  ownedUsed : ∀ (i : Int) (n : Node) b, state.inodes[i]? = some n → n.Owns b →
    b ∈ state.used ∧ ¬Metadata state b
  disjoint : ∀ (i : Int) (n : Node) (j : Int) (m : Node) b,
    state.inodes[i]? = some n → state.inodes[j]? = some m → n.Owns b → m.Owns b → i = j
  superblockOK : SuperblockOK state.superblock
  region : ∀ (i : Int) (n : Node), state.inodes[i]? = some n →
    0 ≤ i ∧ i / 16 < state.superblock.bmapstart - state.superblock.inodestart
  slot : ∀ (i : Int) (n : Node), state.inodes[i]? = some n → n.SlotInjective
  regionDomain : ∀ i : Int, 0 ≤ i ∧ i < 16 * (state.superblock.ninodes / 16 + 1) →
    state.inodes[i]?.isSome
  directory : ∀ (i : Int) (n : Node), state.inodes[i]? = some n → DurableNode.DirLocal i state.nib n
  domainBelow : ∀ b : Int, disk[b]?.isSome → 0 ≤ b ∧ b < state.superblock.size

def OK (state : State) (disk : BlockMap) : Prop := Bytes state disk ∧ DurableState.Local state
def Holds (disk : BlockMap) : Prop := ∃ state, OK state disk

/-- Source snap_shape has exactly this single field, despite its older header. -/
structure Shape (state : State) (disk : BlockMap) : Prop where
  domainBelow : ∀ b : Int, disk[b]?.isSome → 0 ≤ b ∧ b < state.superblock.size

structure InodeRead (sb : Superblock) (disk : BlockMap) (i : Int) (n : Node) : Prop where
  record : ∃ bytes, disk[sb.inodestart + i / 16]? = some bytes ∧
    RecordInBlock bytes (64 * (i % 16)) n.record
  data : ∀ (k : Nat) bytes, n.blocks[k]? = some bytes → disk[n.address k]? = some bytes
  indirect : n.indirect ≠ 0 → disk[n.indirect]? = some (indirectBytes n.entries)
  slot : n.SlotInjective

end Xv6.Fs.Snapshot
