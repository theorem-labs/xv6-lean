import Xv6.Fs.BitmapProofs
import Xv6.Fs.Image
import Xv6.Generated.BitmapInputs

/-! The actual initial bitmap block, as a kernel-checked literal input.
Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Xv6.Fs.Image

abbrev initialBitmapBytes := Xv6.Generated.Bitmap.bitmapBytes

theorem initial_bitmap_bytes : blockView superblock.bmapstart = initialBitmapBytes := by decide

private theorem initial_bitmap_bits :
    (List.range 2000).all (fun i => bitmapBit initialBitmapBytes (i : Int) == decide (i < 983)) = true := by
  decide

theorem initial_bitmap_bit (b : Int) (bound : 0 ≤ b ∧ b < 2000) :
    bitmapBit (blockView superblock.bmapstart) b = decide (b < 983) := by
  rw [initial_bitmap_bytes]
  have h := List.all_eq_true.mp initial_bitmap_bits b.toNat (List.mem_range.mpr (by omega))
  have cast : (b.toNat : Int) = b := Int.toNat_of_nonneg bound.1
  have cmp : (b.toNat < 983) = (b < 983) := propext (by omega)
  simpa only [cast, cmp, beq_iff_eq] using h

end Xv6.Fs.Image
