import Xv6.Kernel.MycpuDecodeDefs

namespace Xv6.Kernel.MycpuDecode
open MachCSL.Machine MachCSL.Memory
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem bytes_length : bytes.length = 32 := rfl

/-- Exact byte lookup into the imported full ELF, after its first 4096 bytes. -/
theorem file_bytes : ∀ j : Fin 32,
    Images.kernel.getByte? (0x28ba + j.val) = some (bytes[j.val]'(by rw [bytes_length]; exact j.isLt)) := by
  decide

theorem ram_byte (j : Nat) (bound : j < 32) :
    loadedRam Xv6.Machine.bootImage (BitVec.ofInt 64 (base + (j : Int))) =
      some (Xv6.Machine.byteOfUInt8 (bytes[j]'(by rw [bytes_length]; exact bound))) := by
  have low : (ramLow : Int) ≤ base + (j : Int) := by unfold ramLow base; omega
  have high : base + (j : Int) < (ramHigh : Int) := by unfold ramHigh base; omega
  rw [(loadedRam_shape Xv6.Machine.bootImage).2 _ low high]
  change some (Xv6.Machine.bootByte (base + (j : Int))) = _
  rw [Xv6.Machine.bootByte_file _ (by unfold base; omega)]
  have index : 4096 + (base + (j : Int) - 0x80000000).toNat = 0x28ba + j := by unfold base; omega
  rw [index, file_bytes ⟨j, bound⟩]
  rfl

/-- All 32 bytes come from the actual ELF-loaded RAM. No missing address is
filled from the expected code table. -/
theorem ram_bytes : ∀ j : Fin 32,
    loadedRam Xv6.Machine.bootImage (BitVec.ofInt 64 (base + (j.val : Int))) =
      some (Xv6.Machine.byteOfUInt8 (bytes[j.val]'(by rw [bytes_length]; exact j.isLt))) :=
  fun j => ram_byte j.val j.isLt

/-- The fourteen mixed-width rows cover exactly the complete 32-byte body. -/
theorem layout_complete :
    (List.ofFn (fun i : Fin 14 => (List.range (width i)).map (offset i + ·))).flatten = List.range 32 := by
  decide

theorem span_bound : ∀ i : Fin 14, offset i + width i ≤ 32 := by decide

theorem word_bytes : ∀ (i : Fin 14) (j : Fin (width i)),
    nthByte (word i) j.val =
      Xv6.Machine.byteOfUInt8 (bytes[offset i + j.val]'(by
        rw [bytes_length]; have := span_bound i; have := j.isLt; omega)) := by
  decide

theorem instruction_address_add (i : Fin 14) (j : Nat) :
    addressAdd (address i) j = BitVec.ofInt 64 (base + ((offset i + j : Nat) : Int)) := by
  simp only [addressAdd, address, Int.natCast_add, BitVec.ofInt_add, BitVec.ofInt_natCast,
    BitVec.add_assoc]

/-- Actual modular machine reads of every row, from the ELF-derived boot image. -/
theorem instruction_bytes (i : Fin 14) :
    readBytes (loadedRam Xv6.Machine.bootImage) (address i) (width i) = some (word i) := by
  apply readBytes_of_bytes
  intro j bound
  rw [instruction_address_add]
  have inside : offset i + j < 32 := by have := span_bound i; omega
  rw [ram_byte _ inside, word_bytes i ⟨j, bound⟩]

theorem compressed_tag : ∀ i : Fin 14,
    LeanPaperStock.Functions.isRVC (BitVec.ofNat 16 (encoding i)) = compressed i := by decide

end Xv6.Kernel.MycpuDecode
