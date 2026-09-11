import Xv6.Kernel.PushOffCodePureProofs
import Xv6.Kernel.KernelTextImageLink

namespace Xv6.Kernel.PushOffCode
open Iris Iris.BI MachCSL.Machine MachCSL.Memory MachCSL.Logic LeanPaperStock.Functions
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Form the exact source footprint after accounting for the actual aligned
compressed lookahead; no instruction decoder is used by this resource rule. -/
theorem window_instr era tier i :
    iprop(KernelTextDatum.window capacity era tier (pc i) (fetchWidth i) .discard (fetchWord i) ⊢
      KptFetch.instrBytes capacity era tier (pc i) (result i)) := by
  unfold result
  cases hc : compressed i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have fw := fetchWidth_base i hc
    unfold fetchWord
    rw [fw, base_encoding i hc]
    iintro H
    isimp only [Nat.reduceMul] at H
    iunfold KptFetch.instrBytes
    isimp only []
    iframe H
    ipureintro
    exact ⟨aligned i, by rw [lowHalf_ofNat, compressed_opcode, hc]⟩
  | true =>
    simp only [↓reduceIte]
    have fw := fetchWidth_compressed i hc
    cases ha : is_aligned_vaddr (.Virtaddr (pc i)) 4 with
    | false =>
      simp only [ha, Bool.false_eq_true, ↓reduceIte] at fw
      unfold fetchWord
      rw [fw, fetch_low i hc]
      iintro H
      iunfold KptFetch.instrBytes
      isimp only [ha, Bool.false_eq_true, ↓reduceIte]
      iframe H
      ipureintro
      exact ⟨aligned i, by rw [compressed_opcode, hc]⟩
    | true =>
      simp only [ha, ↓reduceIte] at fw
      unfold fetchWord
      rw [fw]
      iintro H
      iunfold KptFetch.instrBytes
      isimp only [ha, ↓reduceIte]
      isplitr
      · ipureintro; exact aligned i
      isplitr
      · ipureintro; rw [compressed_opcode, hc]
      iexists BitVec.ofNat 32 (fetchEncoding i)
      iframe H
      ipureintro
      rw [lowHalf_ofNat, fetch_low i hc]

theorem code era tier i :
    iprop(KernelTextImage.text capacity era tier ⊢
      KernelTextImage.text capacity era tier ∗ KptFetch.instrBytes capacity era tier (pc i) (result i)) := by
  iintro #Htext
  ihave Hwindow := (KernelTextImage.nativeSpec capacity).window era tier (address i)
    (fetchWidth i) (fetchWord i) (fetch_bytes i) $$ Htext
  iframe Htext
  iapply window_instr capacity era tier i
  isimp only [pc]
  iexact Hwindow

end Xv6.Kernel.PushOffCode
