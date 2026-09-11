import Xv6.Fs.Superblock

/-! The source `DinodeEnc` record and byte encoder, and `FsImg` inode and
indirect-block decoders. The address list remains arbitrary; its required
length is a separate predicate, as in the source. -/
namespace Xv6.Fs
open MachCSL.Memory

structure Dinode where
  type : BitVec 16
  major : BitVec 16
  minor : BitVec 16
  nlink : BitVec 16
  size : BitVec 32
  addrs : List (BitVec 32)
  deriving DecidableEq, Repr, Inhabited

def inodeBlock (inum : BitVec 32) (start : Int) : Int := (inum.toNat : Int) / 16 + start
def inodeSlot (inum : BitVec 32) : Nat := inum.toNat % 16

def dinodeBytes (dn : Dinode) : List Byte :=
  halfBytes dn.type ++ halfBytes dn.major ++ halfBytes dn.minor ++ halfBytes dn.nlink ++
    word32Bytes dn.size ++ indirectBytes dn.addrs

def inodeBlockBytes : List Dinode → List Byte
  | [] => []
  | dn :: rest => dinodeBytes dn ++ inodeBlockBytes rest

def Dinode.WellFormed (dn : Dinode) : Prop := dn.addrs.length = 13
def InodeBlockWellFormed (records : List Dinode) : Prop :=
  records.length = 16 ∧ ∀ dn ∈ records, dn.WellFormed

def dinodeWindow (image : Blocks) (sb : Superblock) (inum : Int) : List Byte :=
  (image (inodeBlock (BitVec.ofInt 32 inum) sb.inodestart)).drop
    (64 * inodeSlot (BitVec.ofInt 32 inum))

def decodeDinode (bytes : List Byte) : Dinode :=
  ⟨BitVec.ofInt 16 (leAt bytes 0 2), BitVec.ofInt 16 (leAt bytes 2 2),
    BitVec.ofInt 16 (leAt bytes 4 2), BitVec.ofInt 16 (leAt bytes 6 2),
    BitVec.ofInt 32 (leAt bytes 8 4),
    (List.range 13).map fun j => BitVec.ofInt 32 (leAt bytes (12 + 4 * j) 4)⟩

def dinode (image : Blocks) (sb : Superblock) (inum : Int) : Dinode :=
  decodeDinode (dinodeWindow image sb inum)

def indirectEntries (image : Blocks) (dn : Dinode) : List Int :=
  let ib := ((dn.addrs[12]?.getD 0).toNat : Int)
  if ib == 0 then List.replicate 256 0 else
    let bytes := image ib
    (List.range 256).map fun j => leAt bytes (4 * j) 4

def blockAddress (image : Blocks) (dn : Dinode) (k : Nat) : Int :=
  if k < 12 then ((dn.addrs[k]?.getD 0).toNat : Int)
  else (indirectEntries image dn)[k - 12]?.getD 0

def dataOf (image : Blocks) (dn : Dinode) : Nat → List Byte :=
  let entries := indirectEntries image dn
  fun k =>
    let a := if k < 12 then ((dn.addrs[k]?.getD 0).toNat : Int) else entries[k - 12]?.getD 0
    if a == 0 then List.replicate 1024 0 else image a

def BlocksFull (image : Blocks) : Prop := ∀ block, (image block).length = 1024

theorem inodeSlot_lt (inum : BitVec 32) : inodeSlot inum < 16 := Nat.mod_lt _ (by decide)

theorem dinodeBytes_length (dn : Dinode) (wf : dn.WellFormed) : (dinodeBytes dn).length = 64 := by
  simp [dinodeBytes, halfBytes, word32Bytes, indirectBytes_length, Dinode.WellFormed] at wf ⊢
  omega

theorem inodeBlockBytes_length (records : List Dinode) (wf : ∀ dn ∈ records, dn.WellFormed) :
    (inodeBlockBytes records).length = 64 * records.length := by
  induction records with
  | nil => rfl
  | cons dn rest ih =>
    rw [inodeBlockBytes, List.length_append, dinodeBytes_length dn (wf dn (by simp)),
      ih (fun d hd => wf d (by simp [hd]))]
    simp [Nat.mul_succ, Nat.add_comm]

theorem decodeDinode_wf (bytes : List Byte) : (decodeDinode bytes).WellFormed := by
  simp [decodeDinode, Dinode.WellFormed]

theorem dinode_wf (image : Blocks) (sb : Superblock) (inum : Int) :
    (dinode image sb inum).WellFormed := decodeDinode_wf _

theorem indirectEntries_length (image : Blocks) (dn : Dinode) :
    (indirectEntries image dn).length = 256 := by
  unfold indirectEntries
  dsimp only
  split <;> simp only [List.length_replicate, List.length_map, List.length_range]

theorem dataOf_address (image : Blocks) (dn : Dinode) (k : Nat) :
    dataOf image dn k = if blockAddress image dn k == 0 then List.replicate 1024 0
      else image (blockAddress image dn k) := rfl

theorem dataOf_holes (image : Blocks) (dn : Dinode) (k : Nat)
    (hole : blockAddress image dn k = 0) : dataOf image dn k = List.replicate 1024 0 := by
  rw [dataOf_address, hole]
  rfl

theorem dataOf_sized (image : Blocks) (dn : Dinode) (full : BlocksFull image) (k : Nat) :
    (dataOf image dn k).length = 1024 := by
  rw [dataOf_address]
  split
  · exact List.length_replicate ..
  · exact full _

end Xv6.Fs
