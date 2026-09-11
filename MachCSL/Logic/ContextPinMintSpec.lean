import MachCSL.Logic.ContextPinMintDefs

namespace MachCSL.Logic.ContextPinMint
open Iris Iris.BI MachCSL.Memory MachCSL.Machine

/-- Source physical pin mint and receipts. All updates retain the same actual
heap (including metadata), TSO state and, where supplied, running context. -/
structure Spec {GF : BundledGFunctors} (capacity : Capacity GF) : Prop where
  timestamp_bound : ∀ (names : Names) eraImage g a dq e,
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps dq a e -∗
      ⌜e.1 ≤ g.log.length⌝)
  own_bound : ∀ (names : Names) cpu ξ eraImage g a dq byte time, Drained cpu g →
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      Tso.physBytePointsto capacity.heap.ledger names.tso.ledger.bytes a dq byte -∗
      Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps dq a
        (time, Tso.payNone) -∗ contextBit capacity ξ time a -∗ ⌜time ≤ g.views cpu⌝)
  ledger_mint : ∀ (names : Names) eraImage g a byte time bound allowed,
    time ≤ bound → byte ∈ allowed →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoStore.storedByte capacity names a byte time ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      Tso.physLedgerPin capacity.heap.ledger names.tso.ledger a (.own 1) byte time bound allowed)
  view_now : ∀ (names : Names) eraImage g cpu,
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      Tso.Views.viewLB capacity.views names.tso.views names.tso.logLength
        (hartAgent cpu) (g.views cpu) ∗
      Tso.Views.llb capacity.views names.tso.logLength (g.views cpu))
  log_now : ∀ (names : Names) eraImage g,
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      Tso.Views.llb capacity.views names.tso.logLength g.log.length)
  byte : ∀ (names : Names) cpu ξ eraImage g a byte allowed,
    Drained cpu g → byte ∈ allowed →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      TsoContext.physPointsto capacity names ξ a (.own 1) byte ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      (∃ time : Nat, Tso.physLedgerPin capacity.heap.ledger names.tso.ledger a
        (.own 1) byte time (g.views cpu) allowed))
  bytes : ∀ (names : Names) cpu ξ eraImage g a (n : Nat) value sets,
    Drained cpu g → (∀ j, j < n → value j ∈ sets j) →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      contextBytes capacity names ξ a n value ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      pinnedBytes capacity names a n value (g.views cpu) sets)
  word : ∀ (names : Names) cpu ξ eraImage g a (word : BitVec 64) sets,
    Drained cpu g → (∀ j, j < 8 → nthByte word j ∈ sets j) →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      TsoContextWord.pointsto capacity names ξ a (.own 1) word ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      pinnedWord capacity names a word (g.views cpu) sets)
  byte_top : ∀ (names : Names) ξ eraImage g a byte allowed,
    byte ∈ allowed →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.physPointsto capacity names ξ a (.own 1) byte ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      (∃ time : Nat, Tso.physLedgerPin capacity.heap.ledger names.tso.ledger a
        (.own 1) byte time g.log.length allowed))
  bytes_top : ∀ (names : Names) cpu ξ eraImage g a (n : Nat) value sets,
    (∀ j, j < n → value j ∈ sets j) →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      contextBytes capacity names ξ a n value ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      pinnedBytes capacity names a n value g.log.length sets)
  word_top : ∀ (names : Names) cpu ξ eraImage g a (word : BitVec 64) sets,
    (∀ j, j < 8 → nthByte word j ∈ sets j) →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      TsoContextWord.pointsto capacity names ξ a (.own 1) word ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      pinnedWord capacity names a word g.log.length sets)
  byte_boot : ∀ (names : Names) cpu ξ eraImage g a byte allowed,
    hartAgent cpu = 0 → byte ∈ allowed →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      TsoContext.physPointsto capacity names ξ a (.own 1) byte ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      bootByte capacity names g a byte allowed)
  bytes_boot : ∀ (names : Names) cpu ξ eraImage g a (n : Nat) value sets,
    hartAgent cpu = 0 → (∀ j, j < n → value j ∈ sets j) →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      contextBytes capacity names ξ a n value ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      bootBytes capacity names g a n value sets)
  word_boot : ∀ (names : Names) cpu ξ eraImage g a (word : BitVec 64) sets,
    hartAgent cpu = 0 → (∀ j, j < 8 → nthByte word j ∈ sets j) →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      TsoContextWord.pointsto capacity names ξ a (.own 1) word ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      bootWord capacity names g a word sets)

end MachCSL.Logic.ContextPinMint
