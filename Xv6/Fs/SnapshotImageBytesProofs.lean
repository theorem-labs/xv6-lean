import Xv6.Fs.SnapshotCodecProofs
import Xv6.Fs.DurableImageNodeProofs
import Xv6.Fs.SlotsProofs

/-! Exact image record and held-block byte correspondence from `FsDurImg`
§11a/b. No image-validity or live-inode assumption is needed in this layer. -/
namespace Xv6.Fs
open MachCSL.Memory

theorem recordInBlock_decode (bytes : List Byte) (offset : Nat)
    (bound : offset + 64 ≤ bytes.length) :
    DurableState.RecordInBlock bytes offset (decodeDinode (bytes.drop offset)) := by
  refine ⟨bytes.take offset, (bytes.drop offset).drop 64, ?_, ?_⟩
  · rw [encode_decodeDinode_prefix _ (by simp only [List.length_drop]; omega),
      List.append_assoc, List.take_append_drop, List.take_append_drop]
  · simp only [List.length_take, Nat.min_eq_left (show offset ≤ bytes.length by omega)]

/-- Source `img_rec_in_blk`: the unsigned inode cast is exact only under
the source 32-bit range premise, which is retained here. -/
theorem image_record_in_block (image : Blocks) (sb : Superblock) (i : Int)
    (full : BlocksFull image) (bound : 0 ≤ i ∧ i < 2 ^ 32) :
    DurableState.RecordInBlock (image (sb.inodestart + i / 16))
      (64 * (i % 16)) (dinode image sb i) := by
  have cast : ((BitVec.ofInt 32 i).toNat : Int) = i := by
    rw [BitVec.toNat_ofInt]
    change ((i % (2 ^ 32 : Int)).toNat : Int) = i
    rw [Int.emod_eq_of_lt bound.1 bound.2, Int.toNat_of_nonneg bound.1]
  have address : inodeBlock (BitVec.ofInt 32 i) sb.inodestart = sb.inodestart + i / 16 := by
    simp only [inodeBlock, cast, Int.add_comm]
  have offset : ((64 * inodeSlot (BitVec.ofInt 32 i) : Nat) : Int) = 64 * (i % 16) := by
    simp only [Int.natCast_mul, Int.cast_ofNat_Int, inodeSlot, Int.natCast_emod, cast]
  have room : 64 * inodeSlot (BitVec.ofInt 32 i) + 64 ≤
      (image (sb.inodestart + i / 16)).length := by
    rw [full]
    have := inodeSlot_lt (BitVec.ofInt 32 i)
    omega
  have result := recordInBlock_decode (image (sb.inodestart + i / 16))
    (64 * inodeSlot (BitVec.ofInt 32 i)) room
  rw [offset] at result
  simpa only [dinode, dinodeWindow, address] using result

/-- The full indirect block, including every entry after file size. -/
theorem indirectEntries_bytes_roundtrip (image : Blocks) (dn : Dinode)
    (full : BlocksFull image) (nonzero : dn.addrZ 12 ≠ 0) :
    indirectBytes ((indirectEntries image dn).map (BitVec.ofInt 32)) = image (dn.addrZ 12) := by
  unfold indirectEntries
  change indirectBytes (List.map (BitVec.ofInt 32)
    (if dn.addrZ 12 == 0 then _ else _)) = _
  rw [if_neg (by simpa only [beq_iff_eq] using nonzero), List.map_map]
  exact indirectBytes_roundtrip (image (dn.addrZ 12)) 256 (full _)

namespace DurableImageNode
open DurableNode

theorem image_node_slot_eq (image : Blocks) (sb : Superblock) (i : Int) (k : Nat)
    (_bound : k ≤ 268) :
    (imageNode image sb i).slot k = Xv6.Fs.slot image (dinode image sb i) k := by
  unfold Node.slot Xv6.Fs.slot
  rw [imageNode_indirect, imageNode_address]

theorem image_node_slot_injective (image : Blocks) (sb : Superblock) (i : Int)
    (injective : Xv6.Fs.SlotInjective image (dinode image sb i)) :
    (imageNode image sb i).SlotInjective := by
  intro k j hk hj nonzero equal
  rw [image_node_slot_eq image sb i k hk] at nonzero
  rw [image_node_slot_eq image sb i k hk, image_node_slot_eq image sb i j hj] at equal
  exact injective k j hk hj nonzero equal

theorem image_node_owns_slot (image : Blocks) (sb : Superblock) (i b : Int)
    (owns : (imageNode image sb i).Owns b) :
    ∃ k : Nat, k ≤ 268 ∧ Xv6.Fs.slot image (dinode image sb i) k = b ∧ b ≠ 0 := by
  rcases owns with ⟨k, present, address⟩ | ⟨nonzero, address⟩
  · rw [imageNode_lookup] at present
    split at present
    · rename_i held
      rw [imageNode_address] at address
      have below : k ≠ 268 := by omega
      exact ⟨k, by omega, by simpa only [Xv6.Fs.slot, if_neg below] using address,
        by rw [← address]; exact held.2⟩
    · contradiction
  · rw [imageNode_indirect] at nonzero address
    exact ⟨268, by omega, by simpa only [Xv6.Fs.slot, ↓reduceIte] using address,
      by rw [← address]; exact nonzero⟩

theorem image_node_data_at (image : Blocks) (sb : Superblock) (i : Int)
    (k : Nat) (bytes : List Byte) (held : (imageNode image sb i).blocks[k]? = some bytes) :
    bytes = image ((imageNode image sb i).address k) ∧
      (imageNode image sb i).Owns ((imageNode image sb i).address k) := by
  constructor
  · rw [imageNode_lookup] at held
    split at held
    · rename_i live
      have equal := Option.some.inj held
      rw [dataOf_address, if_neg (by simpa only [beq_iff_eq] using live.2)] at equal
      rw [imageNode_address]
      exact equal.symm
    · contradiction
  · exact Or.inl ⟨k, by rw [held]; rfl, rfl⟩

theorem image_node_indirect_at (image : Blocks) (sb : Superblock) (i : Int)
    (full : BlocksFull image) (nonzero : (imageNode image sb i).indirect ≠ 0) :
    image ((imageNode image sb i).indirect) = indirectBytes (imageNode image sb i).entries ∧
      (imageNode image sb i).Owns (imageNode image sb i).indirect := by
  constructor
  · rw [imageNode_entries, imageNode_indirect]
    exact (indirectEntries_bytes_roundtrip image _ full nonzero).symm
  · exact Or.inr ⟨nonzero, rfl⟩

end DurableImageNode
end Xv6.Fs
