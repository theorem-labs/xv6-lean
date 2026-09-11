import Xv6.Kernel.PushOffCodeSpec

namespace Xv6.Kernel.PushOffCode
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem body_coverage : (List.finRange 24).flatMap (fun i => (List.range (width i)).map (offset i + ·)) = List.range 58 := by decide
theorem widths : ∀ i, width i = 2 ∨ width i = 4 := by decide
theorem aligned : ∀ i, is_aligned_vaddr (.Virtaddr (pc i)) 2 = true := by decide
theorem compressed_opcode : ∀ i, isRVC (BitVec.ofNat 16 (encoding i)) = compressed i := by decide
theorem fetch_bound : ∀ i, offset i + fetchWidth i ≤ 60 := by decide
theorem final_lookahead : offset ⟨23, by decide⟩ = 56 ∧ fetchWidth ⟨23, by decide⟩ = 4 ∧
    fetchEncoding ⟨23, by decide⟩ = 0x1101b7c5 := by decide
theorem bytes_length : bytes.length = 60 := rfl
theorem bytes_source : ∀ j : Fin 60, KernelTextImage.sourceMap (base + (j.val : Int)) = some bytes[j.val] := by decide
theorem fetch_bytes (i : Index) (j : Nat) (bound : j < fetchWidth i) : ∃ b,
    KernelTextImage.sourceMap (address i + (j : Int)) = some b ∧
      KernelTextImage.value b = nthByte (fetchWord i) j := by
  have finite : ∀ i : Index, ∀ j : Fin (fetchWidth i), ∃ b,
      KernelTextImage.sourceMap (address i + (j.val : Int)) = some b ∧
        KernelTextImage.value b = nthByte (fetchWord i) j.val := by decide
  exact finite i ⟨j,bound⟩
theorem fetch_low : ∀ i, compressed i = true →
    BitVec.ofNat 16 (fetchEncoding i) = BitVec.ofNat 16 (encoding i) := by decide
theorem base_encoding : ∀ i, compressed i = false → fetchEncoding i = encoding i := by decide
theorem call_sites : ∀ site, pc (callIndex site) = PushOffMycpuCalls.pc site ∧
    encoding (callIndex site) = (PushOffMycpuCalls.encoding site).toNat ∧
    normalized (callIndex site) = .JAL (PushOffMycpuCalls.immediate site, .Regidx 1#5) := by
  intro ⟨site, bound⟩
  have cases : site = 0 ∨ site = 1 ∨ site = 2 := by omega
  rcases cases with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl⟩

theorem nativePureSpec : PureSpec := ⟨body_coverage, widths, aligned, compressed_opcode,
  fetch_bound, final_lookahead, bytes_length, bytes_source, fetch_bytes, fetch_low, base_encoding, call_sites⟩

/-- Complete ownership union, including the two bytes beyond the body.
Repeated addresses are intentional persistent overlapping fetch windows. -/
theorem footprint_complete :
    ((List.finRange 24).flatMap (fun i => (List.range (fetchWidth i)).map (offset i + ·))).eraseDups = List.range 60 := by decide

theorem fetchWidth_base : ∀ i, compressed i = false → fetchWidth i = 4 := by decide
theorem fetchWidth_compressed : ∀ i, compressed i = true → fetchWidth i =
    if is_aligned_vaddr (.Virtaddr (pc i)) 4 then 4 else 2 := by decide

theorem lowHalf_ofNat (n : Nat) : KernelTextDatum.lowHalf (BitVec.ofNat 32 n) = BitVec.ofNat 16 n := by
  apply BitVec.eq_of_toNat_eq
  simp [KernelTextDatum.lowHalf, BitVec.extractLsb'_toNat, Nat.mod_mod_of_dvd,
    show 2^16 ∣ 2^32 by decide]

end Xv6.Kernel.PushOffCode
