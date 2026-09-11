import MachCSL.Logic.ContextPinMintLedgerProofs
import MachCSL.Logic.TsoPinnedReadProofs

namespace MachCSL.Logic.ContextPinMint
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Derive the exact anchor before the update. The own-message arm additionally
uses Latest: dirty-set membership alone does not prove a write at this address. -/
theorem boot_anchor (names : Names) cpu ξ eraImage g a byte time
    (boot : hartAgent cpu = 0) :
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      TsoStore.storedByte capacity names a byte time -∗ contextBit capacity ξ time a -∗
      TsoPinnedRead.slotAnchor capacity.tso names.tso a time) := by
  unfold TsoStore.storedByte
  iintro Hheap Htso Hrun ⟨Hbyte, Htime⟩ Hbit
  ihave %lat := latest capacity names eraImage g a (.own 1) byte time $$ Hheap Htso Hbyte Htime
  unfold TsoPinnedRead.slotAnchor
  cases time with
  | zero => ileft; ipureintro; rfl
  | succ i =>
    iright
    unfold TsoContext.ownContext TsoContext.ctxAt
    icases Hrun with ⟨%B, %K, %W, %D, ⟨Hb, Hd⟩, Hview, %bound, _, _, Hoks⟩
    unfold contextBit TsoContext.floor
    icases Hbit with (Hclean | Hdirty)
    · ihave %timeBound := Tso.Views.llb_valid capacity.views ξ.bound (.own 1) B (i + 1) $$ Hb Hclean
      iright
      have gate := Tso.Views.viewLB_le capacity.views names.tso.views names.tso.logLength
        (hartAgent cpu) K (i + 1) (by omega)
      rw [boot] at gate
      ieval (rewrite [boot]) at Hview
      iapply gate $$ Hview
    · ihave %member := Tso.History.dset_lookup capacity.history ξ.dirty 1 D (i + 1, a) $$ Hd Hdirty
      ihave Hok := BigSepS.bigSepS_elem_of member $$ Hoks
      unfold Tso.History.dirtyOK
      icases Hok with (%below | ⟨%index, %msg, %eq, Hentry, %author⟩)
      · iright
        have gate := Tso.Views.viewLB_le capacity.views names.tso.views names.tso.logLength
          (hartAgent cpu) K (i + 1) (by dsimp at below; omega)
        rw [boot] at gate
        ieval (rewrite [boot]) at Hview
        iapply gate $$ Hview
      · ileft
        have same : i = index := by dsimp at eq; omega
        subst index
        unfold Tso.Interp.tsoInterpAt
        icases Htso with ⟨%_timestamps, %entries, _, _, _, Hlog, %rep, _, _, _⟩
        ihave %lookup := Tso.History.log_lookup capacity.history names.tso.logEntries (.own 1)
          entries i msg $$ Hlog Hentry
        have lookup' : g.log[i]? = some msg := by rw [← rep i]; exact lookup
        have wrote : msgByte msg a = some byte := by
          simpa [logByte, lookup'] using lat.2.1
        iapply TsoPinnedRead.ownAnchor_intro capacity.tso names.tso 0 a i msg byte
          wrote (author.trans boot) $$ Hentry

theorem byte_boot : ∀ (names : Names) cpu ξ eraImage g a byte allowed,
    hartAgent cpu = 0 → byte ∈ allowed →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      TsoContext.physPointsto capacity names ξ a (.own 1) byte ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      bootByte capacity names g a byte allowed) := by
  intro names cpu ξ eraImage g a byte allowed boot member
  iintro Hheap Htso Hrun Hbyte
  unfold TsoContext.physPointsto
  icases Hbyte with ⟨%time, Hbyte, Htime, Hbit⟩
  ihave %le := timestamp_bound capacity names eraImage g a (.own 1) (time, Tso.payNone) $$ Htso Htime
  ihave Hstored : TsoStore.storedByte capacity names a byte time $$ [Hbyte Htime]
  · unfold TsoStore.storedByte
    iframe Hbyte Htime
  have anchor := boot_anchor capacity names cpu ξ eraImage g a byte time boot
  unfold contextBit at anchor
  ihave #Hanchor := anchor $$ Hheap Htso Hrun Hstored Hbit
  imod ledger_mint capacity names eraImage g a byte time time allowed (Nat.le_refl _) member
    $$ Hheap Htso Hstored with ⟨Hheap, Htso, Hpin⟩
  imodintro
  iframe Hheap Htso Hrun
  unfold bootByte
  iexists time, time
  iframe Hpin Hanchor
  ipureintro
  exact le

end MachCSL.Logic.ContextPinMint
