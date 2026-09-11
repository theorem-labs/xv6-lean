import Xv6.Kernel.MycpuFetchBytesDefs
import Xv6.Kernel.MycpuDecodeImage

namespace Xv6.Kernel.MycpuFetchBytes
open MachCSL.Machine MachCSL.Memory LeanPaperStock.Functions
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem bytes_length : bytes.length = 34 := rfl

theorem ziccif_enabled : currentlyEnabled .Ext_Ziccif = (pure true : SailM Bool) := by
  rw [currentlyEnabled, hartSupports]

theorem file_bytes : ∀ j : Fin 34,
    Images.kernel.getByte? (0x28ba + j.val) = some (bytes[j.val]'(by rw [bytes_length]; exact j.isLt)) := by
  decide

theorem ram_byte (j : Nat) (bound : j < 34) :
    loadedRam Xv6.Machine.bootImage (BitVec.ofInt 64 (MycpuDecode.base + (j : Int))) =
      some (Xv6.Machine.byteOfUInt8 (bytes[j]'(by rw [bytes_length]; exact bound))) := by
  have low : (ramLow : Int) ≤ MycpuDecode.base + (j : Int) := by unfold ramLow MycpuDecode.base; omega
  have high : MycpuDecode.base + (j : Int) < (ramHigh : Int) := by unfold ramHigh MycpuDecode.base; omega
  rw [(loadedRam_shape Xv6.Machine.bootImage).2 _ low high]
  change some (Xv6.Machine.bootByte (MycpuDecode.base + (j : Int))) = _
  rw [Xv6.Machine.bootByte_file _ (by unfold MycpuDecode.base; omega)]
  have index : 4096 + (MycpuDecode.base + (j : Int) - 0x80000000).toNat = 0x28ba + j := by
    unfold MycpuDecode.base; omega
  rw [index, file_bytes ⟨j, bound⟩]
  rfl

theorem span_bound : ∀ i : Fin 14, MycpuDecode.offset i + width i ≤ 34 := by decide

theorem supported_width : ∀ i : Fin 14, width i = 2 ∨ width i = 4 := by decide

theorem body_width_le : ∀ i : Fin 14, MycpuDecode.width i ≤ width i := by decide

/-- No uncompressed instruction in this body needs the second two-byte branch. -/
theorem base_aligned : ∀ i : Fin 14, MycpuDecode.compressed i = false →
    is_aligned_vaddr (.Virtaddr (MycpuDecode.address i)) 4 = true := by decide

theorem footprint_complete :
    ((List.ofFn (fun i : Fin 14 => (List.range (width i)).map (MycpuDecode.offset i + ·))).flatten).eraseDups =
      List.range 34 := by decide

theorem word_bytes : ∀ (i : Fin 14) (j : Fin (width i)),
    nthByte (word i) j.val =
      Xv6.Machine.byteOfUInt8 (bytes[MycpuDecode.offset i + j.val]'(by
        rw [bytes_length]; have := span_bound i; have := j.isLt; omega)) := by decide

theorem fetched_bytes (i : Fin 14) :
    readBytes (loadedRam Xv6.Machine.bootImage) (MycpuDecode.address i) (width i) = some (word i) := by
  apply readBytes_of_bytes
  intro j bound
  rw [MycpuDecode.instruction_address_add]
  have inside : MycpuDecode.offset i + j < 34 := by have := span_bound i; omega
  rw [ram_byte _ inside, word_bytes i ⟨j, bound⟩]

theorem low_halfword : ∀ i : Fin 14,
    (word i).setWidth 16 = BitVec.ofNat 16 (MycpuDecode.encoding i) := by decide

theorem base_word : ∀ i : Fin 14, MycpuDecode.compressed i = false →
    (word i).setWidth 32 = BitVec.ofNat 32 (MycpuDecode.encoding i) := by decide

theorem last_fetch : width 13 = 4 ∧ word 13 = 0x11018082#32 := by decide

end Xv6.Kernel.MycpuFetchBytes
