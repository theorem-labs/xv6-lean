import Xv6.Fs.DinodeProofs

namespace Xv6.Fs

theorem decodeDinode_congr (left right : List MachCSL.Memory.Byte)
    (same : ∀ j, j < 64 → byteAt left j = byteAt right j) :
    decodeDinode left = decodeDinode right := by
  have readEq (offset count : Nat) (bound : offset + count ≤ 64) :
      leAt left offset count = leAt right offset count := by
    unfold leAt
    apply congrArg Int.ofNat
    apply congrArg MachCSL.Memory.assembleBytes
    apply List.map_congr_left
    intro j hj
    exact same _ (by have := List.mem_range.mp hj; omega)
  unfold decodeDinode
  rw [readEq 0 2 (by decide), readEq 2 2 (by decide), readEq 4 2 (by decide),
    readEq 6 2 (by decide), readEq 8 4 (by decide)]
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [readEq (12 + 4 * q) 4 (by have := List.mem_range.mp hq; omega)]

theorem inodeBlockBytes_byte (records : List Dinode) (i j : Nat)
    (wf : ∀ dn ∈ records, dn.WellFormed) (index : i < records.length) (byte : j < 64) :
    byteAt (inodeBlockBytes records) (64 * i + j) = byteAt (dinodeBytes records[i]) j := by
  induction records generalizing i with
  | nil => simp at index
  | cons dn rest ih =>
    have hd : dn.WellFormed := wf dn (by simp)
    have hr : ∀ d ∈ rest, d.WellFormed := fun d h => wf d (by simp [h])
    cases i with
    | zero =>
      simp only [inodeBlockBytes, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      exact byteAt_append_left _ _ _ (by rw [dinodeBytes_length dn hd]; exact byte)
    | succ i =>
      have hi : i < rest.length := by simpa using index
      change byteAt (dinodeBytes dn ++ inodeBlockBytes rest) (64 * (i + 1) + j) =
        byteAt (dinodeBytes rest[i]) j
      rw [show 64 * (i + 1) + j = (dinodeBytes dn).length + (64 * i + j) by
        rw [dinodeBytes_length dn hd]; omega, byteAt_append_right]
      exact ih i hr hi

/-- Source `fs_dinode_of_diblk`: decoding a slot from an encoded full inode
block returns that very record, with the source total-lookup convention. -/
theorem dinode_of_block (image : Blocks) (sb : Superblock) (inum : Int) (records : List Dinode)
    (wf : InodeBlockWellFormed records)
    (block : image (inodeBlock (BitVec.ofInt 32 inum) sb.inodestart) = inodeBlockBytes records) :
    dinode image sb inum = records[inodeSlot (BitVec.ofInt 32 inum)]?.getD default := by
  have hs := inodeSlot_lt (BitVec.ofInt 32 inum)
  have hi : inodeSlot (BitVec.ofInt 32 inum) < records.length := by rw [wf.1]; exact hs
  have hd := wf.2 records[inodeSlot (BitVec.ofInt 32 inum)] (List.getElem_mem hi)
  simp only [List.getElem?_eq_getElem hi, Option.getD_some]
  rw [← decodeDinode_encode _ hd]
  apply decodeDinode_congr
  intro j hj
  unfold dinodeWindow
  rw [block]
  simp only [byteAt, List.getElem?_drop]
  exact inodeBlockBytes_byte records _ j wf.2 hi hj

end Xv6.Fs
