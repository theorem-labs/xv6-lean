import Xv6.Fs.DinodeBlockProofs

/-! Direct disk-byte forms of the source readers, proved equal to the block/list
forms. They avoid reducing bytes which a field reader never observes. -/
namespace Xv6.Fs

def diskLe (disk : Disk) (address : Int) (count : Nat) : Int :=
  (MachCSL.Memory.assembleBytes ((List.range count).map fun j : Nat =>
    disk (address + j)) : Int)

def inodeAddress (sb : Superblock) (inum : Int) : Int :=
  inodeBlock (BitVec.ofInt 32 inum) sb.inodestart * 1024 +
    (64 * inodeSlot (BitVec.ofInt 32 inum) : Nat)

def diskDinode (disk : Disk) (sb : Superblock) (inum : Int) : Dinode :=
  let a := inodeAddress sb inum
  ⟨BitVec.ofInt 16 (diskLe disk a 2), BitVec.ofInt 16 (diskLe disk (a + 2) 2),
    BitVec.ofInt 16 (diskLe disk (a + 4) 2), BitVec.ofInt 16 (diskLe disk (a + 6) 2),
    BitVec.ofInt 32 (diskLe disk (a + 8) 4),
    (List.range 13).map fun j => BitVec.ofInt 32 (diskLe disk (a + (12 + 4 * j : Nat)) 4)⟩

theorem leAt_dinodeWindow (disk : Disk) (sb : Superblock) (inum : Int)
    (offset count : Nat) (bound : offset + count ≤ 64) :
    leAt (dinodeWindow (blocks disk) sb inum) offset count =
      diskLe disk (inodeAddress sb inum + offset) count := by
  unfold leAt diskLe
  congr 1
  apply congrArg MachCSL.Memory.assembleBytes
  apply List.map_congr_left
  intro j hj
  have hs := inodeSlot_lt (BitVec.ofInt 32 inum)
  have hj := List.mem_range.mp hj
  unfold dinodeWindow
  simp only [byteAt, List.getElem?_drop]
  rw [show ((blocks disk (inodeBlock (BitVec.ofInt 32 inum) sb.inodestart))[
      64 * inodeSlot (BitVec.ofInt 32 inum) + (offset + j)]?).getD 0 =
      disk (inodeBlock (BitVec.ofInt 32 inum) sb.inodestart * 1024 +
        (64 * inodeSlot (BitVec.ofInt 32 inum) + (offset + j) : Nat)) from
    blocks_byte disk _ _ (by omega)]
  congr 1
  simp [inodeAddress, Int.natCast_add, Int.add_assoc]

theorem dinode_blocks (disk : Disk) (sb : Superblock) (inum : Int) :
    dinode (blocks disk) sb inum = diskDinode disk sb inum := by
  unfold dinode decodeDinode diskDinode
  rw [leAt_dinodeWindow disk sb inum 0 2 (by decide),
    leAt_dinodeWindow disk sb inum 2 2 (by decide),
    leAt_dinodeWindow disk sb inum 4 2 (by decide),
    leAt_dinodeWindow disk sb inum 6 2 (by decide),
    leAt_dinodeWindow disk sb inum 8 4 (by decide)]
  rw [show inodeAddress sb inum + (0 : Nat) = inodeAddress sb inum by omega]
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [leAt_dinodeWindow disk sb inum (12 + 4 * j) 4
    (by have := List.mem_range.mp hj; omega)]

theorem leAt_blocks_diskLe (disk : Disk) (block : Int) (offset count : Nat)
    (bound : offset + count ≤ 1024) :
    leAt (blocks disk block) offset count = diskLe disk (block * 1024 + offset) count := by
  rw [leAt_blocks disk block offset count bound]
  simp [diskLe, Int.natCast_add, Int.add_assoc]

def diskIndirectEntries (disk : Disk) (dn : Dinode) : List Int :=
  let ib : Int := (dn.addrs[12]?.getD 0).toNat
  if ib == 0 then List.replicate 256 0 else
    (List.range 256).map fun j => diskLe disk (ib * 1024 + (4 * j : Nat)) 4

theorem indirectEntries_blocks (disk : Disk) (dn : Dinode) :
    indirectEntries (blocks disk) dn = diskIndirectEntries disk dn := by
  unfold indirectEntries diskIndirectEntries
  dsimp only
  split
  · rfl
  · apply List.map_congr_left
    intro j hj
    exact leAt_blocks_diskLe disk _ (4 * j) 4 (by have := List.mem_range.mp hj; omega)

end Xv6.Fs
