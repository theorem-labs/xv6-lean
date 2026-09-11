import Xv6.Kernel.PushOffCodeDefs

namespace Xv6.Kernel.PushOffCode
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions

structure PureSpec : Prop where
  body_coverage : (List.finRange 24).flatMap (fun i => (List.range (width i)).map (offset i + ·)) = List.range 58
  widths : ∀ i, width i = 2 ∨ width i = 4
  aligned : ∀ i, is_aligned_vaddr (.Virtaddr (pc i)) 2 = true
  compressed_opcode : ∀ i, isRVC (BitVec.ofNat 16 (encoding i)) = compressed i
  fetch_bound : ∀ i, offset i + fetchWidth i ≤ 60
  final_lookahead : offset ⟨23, by decide⟩ = 56 ∧ fetchWidth ⟨23, by decide⟩ = 4 ∧
    fetchEncoding ⟨23, by decide⟩ = 0x1101b7c5
  bytes_length : bytes.length = 60
  bytes_source : ∀ j : Fin 60, KernelTextImage.sourceMap (base + (j.val : Int)) = some bytes[j.val]
  fetch_bytes : ∀ i j, j < fetchWidth i → ∃ b,
    KernelTextImage.sourceMap (address i + (j : Int)) = some b ∧
      KernelTextImage.value b = nthByte (fetchWord i) j
  fetch_low : ∀ i, compressed i = true →
    BitVec.ofNat 16 (fetchEncoding i) = BitVec.ofNat 16 (encoding i)
  base_encoding : ∀ i, compressed i = false → fetchEncoding i = encoding i
  call_sites : ∀ site, pc (callIndex site) = PushOffMycpuCalls.pc site ∧
    encoding (callIndex site) = (PushOffMycpuCalls.encoding site).toNat ∧
    normalized (callIndex site) = .JAL (PushOffMycpuCalls.immediate site, .Regidx 1#5)

/-- Preserve the original tier: actual successful source bytes supply the
exact native fetch-resource shape, including mandatory lookahead bytes. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  code : ∀ era tier i,
    iprop(KernelTextImage.text capacity era tier ⊢
      KernelTextImage.text capacity era tier ∗ KptFetch.instrBytes capacity era tier (pc i) (result i))

end Xv6.Kernel.PushOffCode
