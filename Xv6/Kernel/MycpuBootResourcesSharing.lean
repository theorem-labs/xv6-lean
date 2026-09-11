import Xv6.Kernel.MycpuBootResourcesProofs
import MachCSL.Logic.TsoContextBytesProofs

namespace Xv6.Kernel.MycpuBootResources
open Iris Iris.BI MachCSL.Memory MachCSL.Machine MachCSL.Logic
variable {GF : BundledGFunctors} (capacity : TsoStore.Capacity GF) (names : TsoStore.Names)

/-- Both fractions remain owned until the caller explicitly chooses persistence. -/
theorem context_intro (ξ : TsoContext.CtxId) :
    rawSpan capacity names ⊢ contextSpan capacity names ξ (.own 1) :=
  TsoContextBytes.of_stored_zero capacity names ξ address 34 spanWord

theorem context_split (ξ : TsoContext.CtxId) (q1 q2 : Qp) :
    iprop(contextSpan capacity names ξ (.own (q1 + q2)) ⊢
      contextSpan capacity names ξ (.own q1) ∗ contextSpan capacity names ξ (.own q2)) :=
  TsoContextBytes.window_split capacity names ξ address 34 spanWord q1 q2

/-- A concrete overlapping fetch borrows its share and returns the entire span. -/
theorem fetch_access (ξ : TsoContext.CtxId) (dq : DFrac) (i : Fin 14) :
    iprop(contextSpan capacity names ξ dq ⊢ fetchWindow capacity names ξ dq i ∗
      (fetchWindow capacity names ξ dq i -∗ contextSpan capacity names ξ dq)) := by
  have rule := TsoContextBytes.subwindow_acc capacity names ξ address 34 dq spanWord
    (MycpuDecode.offset i) (MycpuFetchBytes.width i) (MycpuFetchBytes.word i)
    (MycpuFetchBytes.span_bound i) (fetch_bytes i)
  rw [fetch_address] at rule
  exact rule

/-- Source boot_led_text_persist: consume the existing full timestamp clients. -/
theorem physical_intro :
    iprop(rawSpan capacity names ⊢ |==> physicalSpan capacity names (.own 1)) := by
  iintro H
  iunfold rawSpan at H
  ihave ⟨Hb, Ht⟩ := (BootWindow.storedWindow_split capacity names address 34 spanWord 0).mp $$ H
  have persist := TsoRead.pristine_window_mint capacity.heap.ledger names.tso.ledger.timestamps address 34
  change iprop(BootWindow.timeWindow capacity.heap.ledger names.tso.ledger.timestamps address 34 0 ⊢
    |==> TsoRead.pristineWindow capacity.heap.ledger names.tso.ledger.timestamps address 34) at persist
  imod persist $$ Ht with Ht
  imodintro
  unfold physicalSpan
  iframe

/-- Only bytes split here; the timestamp-zero resource is already persistent. -/
theorem physical_split (q1 q2 : Qp) :
    iprop(physicalSpan capacity names (.own (q1 + q2)) ⊢
      physicalSpan capacity names (.own q1) ∗ physicalSpan capacity names (.own q2)) := by
  haveI : Fractional (fun q => TsoRead.byteWindow capacity.heap.ledger names.tso.ledger.bytes
      address 34 (.own q) spanWord) := by unfold TsoRead.byteWindow; infer_instance
  unfold physicalSpan
  iintro ⟨Hb, #Ht⟩
  ihave ⟨Hb1, Hb2⟩ := (Fractional.fractional
    (Φ := fun q => TsoRead.byteWindow capacity.heap.ledger names.tso.ledger.bytes address 34 (.own q) spanWord)
    q1 q2).mp $$ Hb
  iframe Hb1 Hb2 Ht

/-- The byte camera's native persistence update consumes its old fragment. -/
theorem physical_persist (dq : DFrac) :
    iprop(physicalSpan capacity names dq ⊢ |==> physicalSpan capacity names .discard) := by
  unfold physicalSpan TsoRead.byteWindow
  iintro ⟨Hb, Ht⟩
  ihave Hb : (|==> [∗list] j ∈ List.range 34,
      Tso.physBytePointsto capacity.heap.ledger names.tso.ledger.bytes
        (addressAdd address j) .discard (nthByte spanWord j)) $$ [Hb]
  · iapply BigSepL.bigSepL_bupd
    iapply BigSepL.bigSepL_mono $$ Hb
    intro _ j _
    unfold Tso.physBytePointsto
    iintro ⟨Hb, %ram⟩
    letI := capacity.heap.ledger.bytes
    imod ghost_map_elem_persist (GF := GF) (K := PhysicalAddress) (V := Byte) (H := Tso.AddressMap)
      names.tso.ledger.bytes (addressAdd address j) dq (nthByte spanWord j) $$ Hb with Hb
    imodintro
    iframe Hb
    ipureintro; exact ram
  · imod Hb with Hb
    imodintro
    iframe

instance physical_persistent : Persistent (physicalSpan capacity names .discard) := by
  letI := capacity.heap.ledger.bytes
  letI := capacity.heap.ledger.timestamps
  unfold physicalSpan TsoRead.byteWindow TsoRead.pristineWindow TsoRead.pristineByte Tso.physBytePointsto
  infer_instance

/-- Discarded timestamps are converted only to discarded context windows. -/
theorem discarded_context (ξ : TsoContext.CtxId) :
    physicalSpan capacity names .discard ⊢ contextSpan capacity names ξ .discard :=
  TsoContextBytes.of_pristine_discard capacity names ξ address 34 spanWord

instance fetch_persistent (ξ : TsoContext.CtxId) (i : Fin 14) :
    Persistent (fetchWindow capacity names ξ .discard i) := by unfold fetchWindow; infer_instance

instance fetchWindows_persistent (ξ : TsoContext.CtxId) :
    Persistent (fetchWindows capacity names ξ) := by unfold fetchWindows; infer_instance

/-- Persistent sharing legitimately retains the span and all overlapping windows. -/
theorem discarded_windows (ξ : TsoContext.CtxId) :
    iprop(physicalSpan capacity names .discard ⊢
      physicalSpan capacity names .discard ∗ fetchWindows capacity names ξ) := by
  iintro #H
  iframe H
  unfold fetchWindows
  induction List.finRange 14 with
  | nil => iapply BigSepL.bigSepL_nil.mpr; itrivial
  | cons i rest ih =>
    iapply BigSepL.bigSepL_cons.mpr
    isplit
    · ihave Hspan := discarded_context capacity names ξ $$ H
      ihave ⟨Hi, _⟩ := fetch_access capacity names ξ .discard i $$ Hspan
      iexact Hi
    · exact ih

/-- No hart or context is privileged by the persistent physical slice. -/
theorem discarded_contexts (contexts : List TsoContext.CtxId) :
    iprop(physicalSpan capacity names .discard ⊢
      physicalSpan capacity names .discard ∗
      ([∗list] ξ ∈ contexts, fetchWindows capacity names ξ)) := by
  iintro #H
  iframe H
  induction contexts with
  | nil => iapply BigSepL.bigSepL_nil.mpr; itrivial
  | cons ξ rest ih =>
    iapply BigSepL.bigSepL_cons.mpr
    isplit
    · ihave ⟨_, Hw⟩ := discarded_windows capacity names ξ $$ H
      iexact Hw
    · exact ih

theorem share : iprop(rawSpan capacity names ⊢ |==> physicalSpan capacity names .discard) := by
  iintro H
  imod physical_intro capacity names $$ H with H
  iapply physical_persist capacity names (.own 1) $$ H

end Xv6.Kernel.MycpuBootResources
