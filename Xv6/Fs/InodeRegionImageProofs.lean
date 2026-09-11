import Xv6.Fs.InodeRegionImageDefs
import Xv6.Fs.SnapshotConfigDecodeProofs
import Xv6.Fs.DinodeBlockProofs

namespace Xv6.Fs.InodeRegionImage
open SnapshotConfig

theorem image_dinode_slot blocks (bi i : Nat) (bound : i < 16) :
    imageDinode blocks (16 * (bi : Int) + (i : Int)) = (blocks[bi]?.getD [])[i]?.getD default := by
  have quotient : (16 * (bi : Int) + (i : Int)) / 16 = bi := by omega
  have remainder : (16 * (bi : Int) + (i : Int)) % 16 = i := by omega
  simp [imageDinode, quotient, remainder]

theorem image_dinode_fs_dinode (image : Blocks) (sb : Superblock) (blocks : List (List Dinode))
    (nib : Nat) i (length : blocks.length = nib)
    (wellFormed : ∀ records ∈ blocks, InodeBlockWellFormed records)
    (encoded : ∀ bi : Nat, bi < nib → image (sb.inodestart + (bi : Int)) = inodeBlockBytes (blocks[bi]?.getD []))
    (range : 0 ≤ i ∧ i < 16 * (nib : Int)) (bound : 16 * (nib : Int) ≤ 2 ^ 32) :
    imageDinode blocks i = dinode image sb i := by
  have index : (i / 16).toNat < nib := by omega
  have index' : (i / 16).toNat < blocks.length := by omega
  have member : blocks[(i / 16).toNat]?.getD [] ∈ blocks := by
    simpa only [List.getElem?_eq_getElem index', Option.getD_some] using List.getElem_mem index'
  have wf := wellFormed _ member
  have cast : ((BitVec.ofInt 32 i).toNat : Int) = i := by
    rw [BitVec.toNat_ofInt]
    change ((i % (2 ^ 32 : Int)).toNat : Int) = i
    rw [Int.emod_eq_of_lt range.1 (by omega), Int.toNat_of_nonneg range.1]
  have address : inodeBlock (BitVec.ofInt 32 i) sb.inodestart = sb.inodestart + ((i / 16).toNat : Int) := by
    unfold inodeBlock
    omega
  have slot : inodeSlot (BitVec.ofInt 32 i) = (i % 16).toNat := by
    unfold inodeSlot
    omega
  rw [dinode_of_block image sb i _ wf (by rw [address]; exact encoded _ index), slot]
  rfl

theorem ireg_bare_of_fn_bare (n : DurableNode.Node) (h : n.Bare) : bare n.record :=
  ⟨h.2.2.2.1, h.1⟩

/-- Bare is independent of type and link count, as in the source. -/
theorem bare_fields (record : Dinode) : bare record ↔
    record.sizeZ = 0 ∧ record.addrs = List.replicate 13 0 := Iff.rfl

theorem image_dinode_empty i : imageDinode [] i = default := by simp [imageDinode]

/-- Signed division/modulo and total lookup agree with the source even
outside the nonnegative region used by the allocation prerequisites. -/
theorem image_dinode_negative_one blocks : imageDinode blocks (-1) =
    (blocks[0]?.getD [])[15]?.getD default := rfl

end Xv6.Fs.InodeRegionImage
