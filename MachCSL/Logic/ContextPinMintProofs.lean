import MachCSL.Logic.ContextPinMintBootProofs

namespace MachCSL.Logic.ContextPinMint
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Machine
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem byte : ∀ (names : Names) cpu ξ eraImage g a byte allowed,
    Drained cpu g → byte ∈ allowed →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      TsoContext.physPointsto capacity names ξ a (.own 1) byte ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      (∃ time : Nat, Tso.physLedgerPin capacity.heap.ledger names.tso.ledger a
        (.own 1) byte time (g.views cpu) allowed)) := by
  intro names cpu ξ eraImage g a byte allowed drained member
  iintro Hheap Htso Hrun Hbyte
  unfold TsoContext.physPointsto
  icases Hbyte with ⟨%time, Hbyte, Htime, Hbit⟩
  have own := own_bound capacity names cpu ξ eraImage g a (.own 1) byte time drained
  unfold contextBit at own
  ihave %le := own $$ Htso Hrun Hbyte Htime Hbit
  ihave Hstored : TsoStore.storedByte capacity names a byte time $$ [Hbyte Htime]
  · unfold TsoStore.storedByte
    iframe Hbyte Htime
  imod ledger_mint capacity names eraImage g a byte time (g.views cpu) allowed le member
    $$ Hheap Htso Hstored with ⟨Hheap, Htso, Hpin⟩
  imodintro
  iframe Hheap Htso Hrun
  iexists time
  iexact Hpin

theorem byte_top : ∀ (names : Names) ξ eraImage g a byte allowed,
    byte ∈ allowed →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.physPointsto capacity names ξ a (.own 1) byte ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      (∃ time : Nat, Tso.physLedgerPin capacity.heap.ledger names.tso.ledger a
        (.own 1) byte time g.log.length allowed)) := by
  intro names ξ eraImage g a byte allowed member
  iintro Hheap Htso Hbyte
  unfold TsoContext.physPointsto
  icases Hbyte with ⟨%time, Hbyte, Htime, _⟩
  ihave %le := timestamp_bound capacity names eraImage g a (.own 1) (time, Tso.payNone) $$ Htso Htime
  ihave Hstored : TsoStore.storedByte capacity names a byte time $$ [Hbyte Htime]
  · unfold TsoStore.storedByte
    iframe Hbyte Htime
  imod ledger_mint capacity names eraImage g a byte time g.log.length allowed le member
    $$ Hheap Htso Hstored with ⟨Hheap, Htso, Hpin⟩
  imodintro
  iframe Hheap Htso
  iexists time
  iexact Hpin

theorem bytes : ∀ (names : Names) cpu ξ eraImage g a (n : Nat) value sets,
    Drained cpu g → (∀ j, j < n → value j ∈ sets j) →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      contextBytes capacity names ξ a n value ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      pinnedBytes capacity names a n value (g.views cpu) sets) := by
  intro names cpu ξ eraImage g a n value sets drained member
  induction n with
  | zero =>
    unfold contextBytes pinnedBytes
    simp only [List.range_zero, BigSepL.bigSepL_nil.to_eq]
    iintro Hheap Htso Hrun _
    imodintro
    iframe Hheap Htso Hrun
  | succ n ih =>
    have smaller : ∀ j, j < n → value j ∈ sets j := fun j hj => member j (by omega)
    have last := member n (Nat.lt_succ_self n)
    iintro Hheap Htso Hrun Hbytes
    iunfold contextBytes at Hbytes
    ieval (rewrite [List.range_succ, BigSepL.bigSepL_append.to_eq, BigSepL.bigSepL_singleton.to_eq]) at Hbytes
    icases Hbytes with ⟨Hbytes, Hlast⟩
    have prior := ih smaller
    unfold contextBytes at prior
    imod prior $$ Hheap Htso Hrun Hbytes with ⟨Hheap, Htso, Hrun, Hbytes⟩
    imod byte capacity names cpu ξ eraImage g (addressAdd a n) (value n) (sets n) drained last
      $$ Hheap Htso Hrun Hlast with ⟨Hheap, Htso, Hrun, Hlast⟩
    imodintro
    iframe Hheap Htso Hrun
    unfold pinnedBytes
    rw [List.range_succ, BigSepL.bigSepL_append.to_eq, BigSepL.bigSepL_singleton.to_eq]
    iframe Hbytes Hlast

theorem word : ∀ (names : Names) cpu ξ eraImage g a (word : BitVec 64) sets,
    Drained cpu g → (∀ j, j < 8 → nthByte word j ∈ sets j) →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      TsoContextWord.pointsto capacity names ξ a (.own 1) word ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      pinnedWord capacity names a word (g.views cpu) sets) := by
  intro names cpu ξ eraImage g a word sets drained member
  unfold TsoContextWord.pointsto
  iintro Hheap Htso Hrun ⟨%aligned, Hbytes⟩
  have mint := bytes capacity names cpu ξ eraImage g a 8 (nthByte word) sets drained member
  unfold contextBytes at mint
  imod mint $$ Hheap Htso Hrun Hbytes with ⟨Hheap, Htso, Hrun, Hbytes⟩
  imodintro
  iframe Hheap Htso Hrun
  unfold pinnedWord
  iframe Hbytes
  ipureintro
  exact aligned

theorem bytes_top : ∀ (names : Names) cpu ξ eraImage g a (n : Nat) value sets,
    (∀ j, j < n → value j ∈ sets j) →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      contextBytes capacity names ξ a n value ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      pinnedBytes capacity names a n value g.log.length sets) := by
  intro names cpu ξ eraImage g a n value sets member
  induction n with
  | zero =>
    unfold contextBytes pinnedBytes
    simp only [List.range_zero, BigSepL.bigSepL_nil.to_eq]
    iintro Hheap Htso Hrun _
    imodintro
    iframe Hheap Htso Hrun
  | succ n ih =>
    have smaller : ∀ j, j < n → value j ∈ sets j := fun j hj => member j (by omega)
    have last := member n (Nat.lt_succ_self n)
    iintro Hheap Htso Hrun Hbytes
    iunfold contextBytes at Hbytes
    ieval (rewrite [List.range_succ, BigSepL.bigSepL_append.to_eq, BigSepL.bigSepL_singleton.to_eq]) at Hbytes
    icases Hbytes with ⟨Hbytes, Hlast⟩
    have prior := ih smaller
    unfold contextBytes at prior
    imod prior $$ Hheap Htso Hrun Hbytes with ⟨Hheap, Htso, Hrun, Hbytes⟩
    imod byte_top capacity names ξ eraImage g (addressAdd a n) (value n) (sets n) last
      $$ Hheap Htso Hlast with ⟨Hheap, Htso, Hlast⟩
    imodintro
    iframe Hheap Htso Hrun
    unfold pinnedBytes
    rw [List.range_succ, BigSepL.bigSepL_append.to_eq, BigSepL.bigSepL_singleton.to_eq]
    iframe Hbytes Hlast

theorem word_top : ∀ (names : Names) cpu ξ eraImage g a (word : BitVec 64) sets,
    (∀ j, j < 8 → nthByte word j ∈ sets j) →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      TsoContextWord.pointsto capacity names ξ a (.own 1) word ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      pinnedWord capacity names a word g.log.length sets) := by
  intro names cpu ξ eraImage g a word sets member
  unfold TsoContextWord.pointsto
  iintro Hheap Htso Hrun ⟨%aligned, Hbytes⟩
  have mint := bytes_top capacity names cpu ξ eraImage g a 8 (nthByte word) sets member
  unfold contextBytes at mint
  imod mint $$ Hheap Htso Hrun Hbytes with ⟨Hheap, Htso, Hrun, Hbytes⟩
  imodintro
  iframe Hheap Htso Hrun
  unfold pinnedWord
  iframe Hbytes
  ipureintro
  exact aligned

theorem bytes_boot : ∀ (names : Names) cpu ξ eraImage g a (n : Nat) value sets,
    hartAgent cpu = 0 → (∀ j, j < n → value j ∈ sets j) →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      contextBytes capacity names ξ a n value ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      bootBytes capacity names g a n value sets) := by
  intro names cpu ξ eraImage g a n value sets boot member
  induction n with
  | zero =>
    unfold contextBytes bootBytes
    unfold TsoPinnedRead.slotBytes
    simp only [List.range_zero, BigSepL.bigSepL_nil.to_eq]
    iintro Hheap Htso Hrun _
    imodintro
    iframe Hheap Htso Hrun
  | succ n ih =>
    have smaller : ∀ j, j < n → value j ∈ sets j := fun j hj => member j (by omega)
    have last := member n (Nat.lt_succ_self n)
    iintro Hheap Htso Hrun Hbytes
    iunfold contextBytes at Hbytes
    ieval (rewrite [List.range_succ, BigSepL.bigSepL_append.to_eq, BigSepL.bigSepL_singleton.to_eq]) at Hbytes
    icases Hbytes with ⟨Hbytes, Hlast⟩
    have prior := ih smaller
    unfold contextBytes at prior
    imod prior $$ Hheap Htso Hrun Hbytes with ⟨Hheap, Htso, Hrun, Hbytes⟩
    imod byte_boot capacity names cpu ξ eraImage g (addressAdd a n) (value n) (sets n) boot last
      $$ Hheap Htso Hrun Hlast with ⟨Hheap, Htso, Hrun, Hlast⟩
    imodintro
    iframe Hheap Htso Hrun
    unfold bootBytes
    unfold TsoPinnedRead.slotBytes
    iunfold bootByte at Hlast
    rw [List.range_succ, BigSepL.bigSepL_append.to_eq, BigSepL.bigSepL_singleton.to_eq]
    iframe Hbytes Hlast

theorem word_boot : ∀ (names : Names) cpu ξ eraImage g a (word : BitVec 64) sets,
    hartAgent cpu = 0 → (∀ j, j < 8 → nthByte word j ∈ sets j) →
    iprop(⊢ TsoContext.heapAt capacity names g -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      TsoContext.ownContext capacity names cpu ξ -∗
      TsoContextWord.pointsto capacity names ξ a (.own 1) word ==∗
      TsoContext.heapAt capacity names g ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g ∗
      TsoContext.ownContext capacity names cpu ξ ∗
      bootWord capacity names g a word sets) := by
  intro names cpu ξ eraImage g a word sets boot member
  unfold TsoContextWord.pointsto
  iintro Hheap Htso Hrun ⟨%aligned, Hbytes⟩
  have mint := bytes_boot capacity names cpu ξ eraImage g a 8 (nthByte word) sets boot member
  unfold contextBytes at mint
  imod mint $$ Hheap Htso Hrun Hbytes with ⟨Hheap, Htso, Hrun, Hbytes⟩
  imodintro
  iframe Hheap Htso Hrun
  unfold bootWord
  iframe Hbytes
  ipureintro
  exact aligned

end MachCSL.Logic.ContextPinMint
