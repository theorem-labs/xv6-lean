import MachCSL.Logic.ContextPinMintPureProofs
import MachCSL.Logic.TsoContextProofs

namespace MachCSL.Logic.ContextPinMint
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem timestamp_bound : ∀ (names : Names) eraImage g a dq e,
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps dq a e -∗
      ⌜e.1 ≤ g.log.length⌝) := by
  intro names eraImage g a dq e
  iintro Htso Htime
  ihave %valid := Tso.Interp.tsoInterpAt_timestamp_valid capacity.tso names.tso eraImage g a dq e $$ Htso Htime
  obtain ⟨byte, _, latest⟩ := Tso.timestampOK_latest valid
  ipureintro
  exact logByte_some_le g.image g.log e.1 a byte latest.1

theorem latest (names : Names) eraImage g a dq byte time :
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      Tso.physBytePointsto capacity.heap.ledger names.tso.ledger.bytes a dq byte -∗
      Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps dq a
        (time, Tso.payNone) -∗ ⌜g.memory a = some byte ∧ Latest g.image g.log a time byte⌝) := by
  unfold TsoContext.heapAt
  iintro ⟨%memory, Hheap, %decoded⟩ Htso ⟨Hbyte, _⟩ Htime
  have heapValid := Heap.valid capacity.heap names.heap memory a dq byte
  rw [Heap.pointsto_eq_byteElem] at heapValid
  ihave %lookup := heapValid $$ Hheap Hbyte
  ihave %valid := Tso.Interp.tsoInterpAt_timestamp_valid capacity.tso names.tso eraImage g a dq
    (time, Tso.payNone) $$ Htso Htime
  obtain ⟨actual, value, lat⟩ := Tso.timestampOK_latest valid
  have stored : g.memory a = some byte := by rw [← decoded]; exact lookup
  have equal : actual = byte := Option.some.inj (value.symm.trans stored)
  subst actual
  ipureintro
  exact ⟨stored, lat⟩

theorem ledger_mint : ∀ (names : Names) eraImage g a byte time bound allowed,
    time ≤ bound → byte ∈ allowed →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoStore.storedByte capacity names a byte time ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      Tso.physLedgerPin capacity.heap.ledger names.tso.ledger a (.own 1) byte time bound allowed) := by
  intro names eraImage g a byte time bound allowed le member
  unfold TsoStore.storedByte
  iintro Hheap Htso ⟨Hbyte, Htime⟩
  ihave %lat := latest capacity names eraImage g a (.own 1) byte time $$ Hheap Htso Hbyte Htime
  unfold Tso.Interp.tsoInterpAt
  icases Htso with ⟨%timestamps, %entries, Hauth, %dom, %ok, Hlog, %rep, Hlen, Hviews, %wf⟩
  imod Tso.timestamp_update capacity.heap.ledger names.tso.ledger.timestamps timestamps a
    (time, Tso.payNone) (time, Tso.payPin allowed bound) $$ Hauth Htime with ⟨Hauth, Htime⟩
  imodintro
  iframe Hheap
  isplitl [Hauth Hlog Hlen Hviews]
  · iexists (PartialMap.insert timestamps a (time, Tso.payPin allowed bound)), entries
    iframe Hauth Hlog Hlen Hviews
    ipureintro
    exact ⟨pin_insert_domain timestamps g.memory a _ dom ⟨byte, lat.1⟩,
      pin_insert_ok timestamps g.image g.memory g.log a byte time bound allowed ok lat.1 lat.2 le member,
      rep, wf⟩
  · unfold Tso.physLedgerPin
    iframe Hbyte Htime

theorem own_bound : ∀ (names : Names) cpu ξ eraImage g a dq byte time, Drained cpu g →
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      Tso.physBytePointsto capacity.heap.ledger names.tso.ledger.bytes a dq byte -∗
      Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps dq a
        (time, Tso.payNone) -∗ contextBit capacity ξ time a -∗ ⌜time ≤ g.views cpu⌝) := by
  intro names cpu ξ eraImage g a dq byte time drained
  unfold TsoContext.ownContext TsoContext.ctxAt contextBit TsoContext.floor Tso.Interp.tsoInterpAt
  iintro ⟨%_timestamps, %entries, _, _, _, Hlog, %rep, _, Hv, _⟩
    ⟨%B, %K, %W, %D, ⟨Hb, Hd⟩, Hview, %bound, _, _, Hoks⟩ _ _ Hbit
  have viewValid := Tso.Views.viewAuth_valid capacity.views names.tso.views names.tso.logLength
    (Tso.Interp.avf g) (hartAgent cpu) K
  rw [Tso.Interp.avf_hart] at viewValid
  ihave %viewBound := viewValid $$ Hv Hview
  icases Hbit with (Hclean | Hdirty)
  · ihave %timeBound := Tso.Views.llb_valid capacity.views ξ.bound (.own 1) B time $$ Hb Hclean
    ipureintro
    omega
  · ihave %member := Tso.History.dset_lookup capacity.history ξ.dirty 1 D (time, a) $$ Hd Hdirty
    ihave Hok := BigSepS.bigSepS_elem_of member $$ Hoks
    unfold Tso.History.dirtyOK
    icases Hok with (%below | ⟨%i, %msg, %eq, Hentry, %author⟩)
    · ipureintro; dsimp at below; omega
    · ihave %lookup := Tso.History.log_lookup capacity.history names.tso.logEntries (.own 1) entries i msg $$ Hlog Hentry
      ipureintro
      rw [rep i] at lookup
      have own := ownPub_ge (hartAgent cpu) g.log i msg lookup author
      dsimp at eq
      exact Nat.le_trans (by omega) drained

theorem view_now : ∀ (names : Names) eraImage g cpu,
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      Tso.Views.viewLB capacity.views names.tso.views names.tso.logLength
        (hartAgent cpu) (g.views cpu) ∗
      Tso.Views.llb capacity.views names.tso.logLength (g.views cpu)) := by
  intro names eraImage g cpu
  unfold Tso.Interp.tsoInterpAt
  iintro ⟨%timestamps, %entries, Hauth, %dom, %ok, Hlog, %rep, Hlen, Hviews, %wf⟩
  have get := Tso.Views.viewLB_get capacity.views names.tso.views names.tso.logLength
    (Tso.Interp.avf g) (hartAgent cpu) g.log.length (Tso.Interp.avf_bound g wf.1 _)
  rw [Tso.Interp.avf_hart] at get
  ihave ⟨Hviews, Hlen, #Hview⟩ := get $$ Hviews Hlen
  ihave #Hlb := Tso.Views.viewLB_llb capacity.views names.tso.views names.tso.logLength
    (hartAgent cpu) (g.views cpu) $$ Hview
  iframe Hview Hlb
  iexists timestamps, entries
  iframe Hauth Hlog Hlen Hviews
  ipureintro
  exact ⟨dom, ok, rep, wf⟩

theorem log_now : ∀ (names : Names) eraImage g,
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      Tso.Views.llb capacity.views names.tso.logLength g.log.length) := by
  intro names eraImage g
  unfold Tso.Interp.tsoInterpAt
  iintro ⟨%timestamps, %entries, Hauth, %dom, %ok, Hlog, %rep, Hlen, Hviews, %wf⟩
  ihave ⟨Hlen, #Hlb⟩ := Tso.Views.llb_get capacity.views names.tso.logLength (.own 1) g.log.length $$ Hlen
  iframe Hlb
  iexists timestamps, entries
  iframe Hauth Hlog Hlen Hviews
  ipureintro
  exact ⟨dom, ok, rep, wf⟩

end MachCSL.Logic.ContextPinMint
