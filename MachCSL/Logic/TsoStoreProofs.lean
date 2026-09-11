import MachCSL.Logic.TsoStoreSpec
import MachCSL.Logic.TsoAppendProofs

namespace MachCSL.Logic.TsoStore
variable {bits : Nat}
open Iris Iris.Std Iris.BI Iris.Algebra MachCSL.Memory MachCSL.Machine
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap

/-- Iris's map union is left biased; Std's concrete union is right biased. -/
theorem union_eq_std (left right : Tso.AddressMap V) :
    Iris.Std.PartialMap.union left right = right ∪ left := by
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro a
  change get? (Iris.Std.PartialMap.union left right) a = (right ∪ left)[a]?
  rw [show get? (Iris.Std.PartialMap.union left right) a =
    (get? left a).orElse (fun _ => get? right a) from get?_union]
  rw [_root_.Std.ExtTreeMap.getElem?_union]
  change left[a]?.orElse (fun _ => right[a]?) = left[a]?.or right[a]?
  cases left[a]? <;> rfl

theorem storeTimestamps_eq_map (new : Tso.AddressMap Byte) (time : Nat) :
    Tso.storeTimestamps new time = Iris.Std.PartialMap.map (fun _ : Byte => (time, Tso.payNone)) new := by
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro a
  change _ = get? (Iris.Std.PartialMap.map (fun _ : Byte => (time, Tso.payNone)) new) a
  simp only [Tso.storeTimestamps, get?_map, _root_.Std.ExtTreeMap.getElem?_map]
  rfl

/-- Finite choice of the existing per-byte existential timestamps. No new
fragment is allocated, and the resulting map has exactly the original domain. -/
theorem collect_exists {GF : BundledGFunctors} (Φ : PhysicalAddress → V → IProp GF)
    (old : Tso.AddressMap Byte) :
    iprop(([∗map] a ↦ _byte ∈ old, ∃ value : V, Φ a value) ⊢
      ∃ chosen : Tso.AddressMap V, ⌜PartialMap.dom chosen = PartialMap.dom old⌝ ∗
        [∗map] a ↦ value ∈ chosen, Φ a value) := by
  induction old using LawfulFiniteMap.induction_on with
  | hemp =>
    iintro _
    iexists (∅ : Tso.AddressMap V)
    isplit
    · ipureintro; funext a; simp [PartialMap.dom, get?_empty]
    · iapply BigSepM.bigSepM_empty.mpr; itrivial
  | hins a byte old absent ih =>
    iintro H
    ihave ⟨⟨%value, Ha⟩, Htail⟩ := (BigSepM.bigSepM_insert absent).1 $$ H
    ihave ⟨%chosen, %domain, Hchosen⟩ := ih $$ Htail
    have missing : get? chosen a = none := by
      have h : ¬ PartialMap.dom chosen a := by rw [domain]; simp [PartialMap.dom, absent]
      cases found : get? chosen a with
      | none => rfl
      | some value => exact False.elim (h (by simp [PartialMap.dom, found]))
    iexists (PartialMap.insert chosen a value)
    isplit
    · ipureintro
      funext b
      apply propext
      simp only [LawfulPartialMap.dom_insert_iff, domain]
    · iapply (BigSepM.bigSepM_insert missing).2
      iframe

theorem transition_memoryOK (before after : State) (new : Tso.AddressMap Byte) (author : Agent)
    (step : Transition before after new author) (ok : MemoryOK before) : MemoryOK after := by
  refine ⟨?_, step.viewsBound, ?_⟩
  · rw [step.image, step.log, flat_append, step.memory, ok.1]
  · simpa only [step.image] using ok.2.2

theorem transition_avf_mono (before after : State) (new : Tso.AddressMap Byte) (author : Agent)
    (step : Transition before after new author) :
    ∀ h, Tso.Interp.avf before h ≤ Tso.Interp.avf after h := by
  intro h
  unfold Tso.Interp.avf
  split
  · exact step.viewsMono _
  · rw [step.log, List.length_append, List.length_singleton]
    omega

variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Bulk replacement keeps the original gen_heap metadata authority. All
old timestamp witnesses are collected from existing owned fragments. -/
theorem ledger_update (names : Names) (memory : Tso.AddressMap Byte)
    (timestamps : Tso.AddressMap Tso.TimestampElem) (old new : Tso.AddressMap Byte)
    (oldLength : Nat) (same : SameDomain old new) :
    iprop(⊢ Heap.interp capacity.heap names.heap memory -∗
      Tso.timestampAuth capacity.heap.ledger names.tso.ledger.timestamps (.own 1) timestamps -∗
      ledgerMap capacity names old ==∗
      ⌜∀ a, PartialMap.dom new a → PartialMap.dom memory a⌝ ∗
      Heap.interp capacity.heap names.heap (memory ∪ new) ∗
      Tso.timestampAuth capacity.heap.ledger names.tso.ledger.timestamps (.own 1)
        (Tso.appendTimestamps timestamps new oldLength) ∗
      storedMap capacity names new (oldLength + 1)) := by
  letI := capacity.heap.native names.heap
  letI := capacity.heap.ledger.timestamps
  iintro Hheap Htimestamps Hledger
  isimp only [Heap.interp, genHeapInterp, genHeapGS.heapName, genHeapGS.metaName,
    Heap.Capacity.native, Names.heap] at Hheap
  icases Hheap with ⟨%metadata, %metaDomain, Hbytes, Hmetadata⟩
  isimp only [ledgerMap, ledgerByte, Tso.physBytePointsto, BigSepM.bigSepM_sep_eq] at Hledger
  icases Hledger with ⟨⟨Hcells, Hram⟩, Htimes⟩
  ihave %ram := BigSepM.bigSepM_pure_intro $$ Hram
  ihave %oldSub := (@ghost_map_lookup_big GF PhysicalAddress Byte Tso.AddressMap inferInstance
    capacity.heap.ledger.bytes names.tso.ledger.bytes (.own 1) memory (.own 1) old) $$ Hbytes Hcells
  have newDomain : ∀ a, PartialMap.dom new a → PartialMap.dom memory a := by
    intro a present
    have presentOld : PartialMap.dom old a := (congrFun same a).mpr present
    obtain ⟨byte, found⟩ := Option.isSome_iff_exists.mp presentOld
    exact Option.isSome_iff_exists.mpr ⟨byte, oldSub a byte found⟩
  have newRam : ∀ a byte, get? new a = some byte → Tso.AddrIsRAM a := by
    intro a byte present
    have domainNew : PartialMap.dom new a := by simp [PartialMap.dom, present]
    have domainOld : PartialMap.dom old a := (congrFun same a).mpr domainNew
    obtain ⟨oldByte, found⟩ := Option.isSome_iff_exists.mp domainOld
    exact ram a oldByte found
  have expose (a : PhysicalAddress) :
      iprop((∃ time : Nat, Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps (.own 1) a (time, Tso.payNone)) ⊢
        ∃ e : Tso.TimestampElem, Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps (.own 1) a e) := by
    iintro H
    icases H with ⟨%time, H⟩
    iexists (time, Tso.payNone)
    iexact H
  ihave Htimes := BigSepM.bigSepM_mono (fun {_ _} _ => expose _) $$ Htimes
  ihave ⟨%oldTimes, %timesDomain, Htimes⟩ := collect_exists
    (fun a e => Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps (.own 1) a e)
    old $$ Htimes
  have sameTimes : PartialMap.dom oldTimes = PartialMap.dom (Tso.storeTimestamps new (oldLength + 1)) := by
    rw [storeTimestamps_eq_map, LawfulPartialMap.dom_map, timesDomain]
    exact same
  imod (@ghost_map_update_big GF PhysicalAddress Byte Tso.AddressMap inferInstance
    capacity.heap.ledger.bytes inferInstance names.tso.ledger.bytes memory old new same)
    $$ Hbytes Hcells with ⟨Hbytes, Hcells⟩
  imod (@ghost_map_update_big GF PhysicalAddress Tso.TimestampElem Tso.AddressMap inferInstance
    capacity.heap.ledger.timestamps inferInstance names.tso.ledger.timestamps timestamps
    oldTimes (Tso.storeTimestamps new (oldLength + 1)) sameTimes)
    $$ Htimestamps Htimes with ⟨Htimestamps, Htimes⟩
  isimp only [Union.union, union_eq_std] at Hbytes
  isimp only [Union.union, union_eq_std] at Htimestamps
  imodintro
  isplit
  · ipureintro; exact newDomain
  isplitl [Hbytes Hmetadata]
  · unfold Heap.interp genHeapInterp
    iexists metadata
    iframe
    ipureintro
    intro a present
    have previous := metaDomain a present
    change (memory[a]?).isSome at previous
    change ((memory ∪ new)[a]?).isSome
    rw [_root_.Std.ExtTreeMap.getElem?_union]
    cases new[a]? with
    | none => exact previous
    | some value => rfl
  isplitl [Htimestamps]
  · unfold Tso.appendTimestamps
    iexact Htimestamps
  · isimp only [storeTimestamps_eq_map, BigOpM.bigOpM_map_eq] at Htimes
    unfold storedMap storedByte Tso.physBytePointsto
    rw [BigSepM.bigSepM_sep_eq, BigSepM.bigSepM_sep_eq]
    iframe Hcells Htimes
    iapply BigSepM.bigSepM_pure.mpr
    ipureintro
    exact newRam

/-- The source ledger store at the complete heap/TSO interpretation. The
successor equations preserve every framed payload and every non-hart view. -/
theorem update (contracts : Contracts capacity) (names : Names) (eraImage : ByteMap 64)
    (before after : State) (old new : Tso.AddressMap Byte) (author : Agent)
    (same : SameDomain old new) (step : Transition before after new author) :
    iprop(⊢ heapAt capacity names before.memory -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ledgerMap capacity names old ==∗
      heapAt capacity names after.memory ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      Tso.History.logElem capacity.history names.tso.logEntries before.log.length
        ⟨FiniteMap.decode new, author⟩ ∗
      storedMap capacity names new (before.log.length + 1)) := by
  iintro Hheap Htso Hledger
  iunfold heapAt at Hheap
  icases Hheap with ⟨%memory, Hheap, %decoded⟩
  iunfold Tso.Interp.tsoInterpAt at Htso
  icases Htso with ⟨%timestamps, %entries, Htimestamps, %domain, %tie, Hlog, %represented, Hlength, Hviews, %ok⟩
  imod ledger_update capacity names memory timestamps old new before.log.length same
    $$ Hheap Htimestamps Hledger with ⟨%_, Hheap, Htimestamps, Hledger⟩
  imod contracts.history.logAppend names.tso.logEntries entries before.log
    ⟨FiniteMap.decode new, author⟩ represented iprop(True) $$ [Hlog] with ⟨Hlog, Hreceipt, _, %represented'⟩
  · iframe
  imod contracts.logGrow names.tso.logLength before.log.length after.log.length
    (by rw [step.log, List.length_append, List.length_singleton]; omega)
    $$ Hlength with ⟨Hlength, _⟩
  imod contracts.views.update names.tso.views (Tso.Interp.avf before) (Tso.Interp.avf after)
    (transition_avf_mono before after new author step) $$ Hviews with Hviews
  imodintro
  isplitl [Hheap]
  · unfold heapAt
    iexists (memory ∪ new)
    iframe
    ipureintro
    rw [step.memory, ← decoded]
    exact FiniteMap.decode_overlay new memory
  isplitl [Htimestamps Hlog Hlength Hviews]
  · unfold Tso.Interp.tsoInterpAt
    iexists (Tso.appendTimestamps timestamps new before.log.length),
      (PartialMap.insert entries before.log.length ⟨FiniteMap.decode new, author⟩)
    iframe
    ipureintro
    refine ⟨?_, ?_, ?_, transition_memoryOK before after new author step ok.1, step.image.trans ok.2⟩
    · rw [step.memory]
      exact Tso.timestampDomain_store before.memory timestamps new before.log.length domain
    · rw [step.image, step.memory, step.log]
      exact Tso.timestampMapOK_store before.image before.memory before.log timestamps new author tie
    · simpa only [step.log] using represented'
  iframe

theorem decode_insert (m : Tso.AddressMap Byte) (a : PhysicalAddress) (byte : Byte) :
    FiniteMap.decode (PartialMap.insert m a byte) = Memory.insert (FiniteMap.decode m) a byte := by
  funext b
  change get? (PartialMap.insert m a byte) b = _
  rw [get?_insert]
  simp only [Memory.insert, overlay, Memory.singleton, FiniteMap.decode]
  by_cases same : a = b <;> simp [same, eq_comm] <;> rfl

theorem windowMap_decode (a : PhysicalAddress) (n : Nat) (word : BitVec bits) :
    FiniteMap.decode (windowMap a n word) = snapshot a n word := by
  have aux (offsets : List Nat) :
      FiniteMap.decode (PartialMap.ofList (offsets.map (fun j => (addressAdd a j, nthByte word j))) : Tso.AddressMap Byte) =
        writeOffsets Memory.empty a word offsets := by
    induction offsets with
    | nil => simp [PartialMap.ofList, FiniteMap.decode_empty, writeOffsets]
    | cons j rest ih =>
      rw [List.map_cons, LawfulPartialMap.ofList_cons, decode_insert, ih]
      rfl
  exact aux (List.range n)

theorem windowMap_sameDomain (a : PhysicalAddress) (n : Nat) (old new : BitVec bits) :
    SameDomain (windowMap a n old) (windowMap a n new) := by
  funext b
  apply propext
  change (FiniteMap.decode (windowMap a n old) b).isSome ↔
    (FiniteMap.decode (windowMap a n new) b).isSome
  rw [windowMap_decode, windowMap_decode, Option.isSome_iff_exists, Option.isSome_iff_exists]
  exact (snapshot_domain a b n old).trans (snapshot_domain a b n new).symm

theorem addressAdd_injective_below (a : PhysicalAddress) (i j : Nat)
    (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (same : addressAdd a i = addressAdd a j) : i = j := by
  have words : BitVec.ofNat 64 i = BitVec.ofNat 64 j := by
    have h := congrArg (fun w : BitVec 64 => w - a) same
    simpa only [addressAdd, BitVec.add_comm a, BitVec.add_sub_cancel] using h
  have values := congrArg BitVec.toNat words
  simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using values

theorem windowEntries_nodup (a : PhysicalAddress) (n : Nat) (word : BitVec bits)
    (bound : n ≤ 2 ^ 64) :
    Iris.Std.NoDupKeys ((List.range n).map (fun j => (addressAdd a j, nthByte word j))) := by
  unfold Iris.Std.NoDupKeys
  rw [List.map_map]
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem _ (List.nodup_range (n := n))
  intro i j hi hj different same
  exact different (addressAdd_injective_below a i j
    (Nat.lt_of_lt_of_le (List.mem_range.mp hi) bound)
    (Nat.lt_of_lt_of_le (List.mem_range.mp hj) bound) same)

theorem window_map (Φ : PhysicalAddress → Byte → IProp GF) (a : PhysicalAddress)
    (n : Nat) (word : BitVec bits) (bound : n ≤ 2 ^ 64) :
    iprop(([∗map] b ↦ byte ∈ windowMap a n word, Φ b byte) ⊣⊢
      [∗list] j ∈ List.range n, Φ (addressAdd a j) (nthByte word j)) := by
  unfold windowMap
  simpa only [BigSepL.bigSepL_map] using
    (BigSepM.bigSepM_ofList (Φ := Φ) (windowEntries_nodup a n word bound))

theorem windowTransition_as_transition (before after : State) (a : PhysicalAddress)
    (n : Nat) (word : BitVec bits) (author : Agent)
    (step : WindowTransition before after a n word author) :
    Transition before after (windowMap a n word) author := by
  refine ⟨step.image, ?_, ?_, step.viewsMono, step.viewsBound⟩
  · simpa only [windowMap_decode] using step.log
  · simpa only [windowMap_decode, writeBytes_overlay] using step.memory

theorem update_window (contracts : Contracts capacity) (names : Names) (eraImage : ByteMap 64)
    (before after : State) (a : PhysicalAddress) (n : Nat) (old new : BitVec bits) (author : Agent)
    (bound : n ≤ 2 ^ 64) (step : WindowTransition before after a n new author) :
    iprop(⊢ heapAt capacity names before.memory -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ledgerWindow capacity names a n old ==∗
      heapAt capacity names after.memory ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      Tso.History.logElem capacity.history names.tso.logEntries before.log.length
        ⟨snapshot a n new, author⟩ ∗
      storedWindow capacity names a n new (before.log.length + 1)) := by
  have input : iprop(ledgerMap capacity names (windowMap a n old) ⊣⊢ ledgerWindow capacity names a n old) :=
    window_map (ledgerByte capacity names) a n old bound
  have output : iprop(storedMap capacity names (windowMap a n new) (before.log.length + 1) ⊣⊢
      storedWindow capacity names a n new (before.log.length + 1)) :=
    window_map (fun b byte => storedByte capacity names b byte (before.log.length + 1)) a n new bound
  iintro Hheap Htso Hwindow
  ihave Hwindow := input.2 $$ Hwindow
  imod update capacity contracts names eraImage before after (windowMap a n old) (windowMap a n new)
    author (windowMap_sameDomain a n old new) (windowTransition_as_transition before after a n new author step)
    $$ Hheap Htso Hwindow with ⟨Hheap, Htso, Hreceipt, Hwindow⟩
  imodintro
  isimp only [windowMap_decode] at Hreceipt
  iframe Hheap Htso Hreceipt
  iapply output.1 $$ Hwindow

/-- Source `phys_ledger_at_ledger`: forget only the exposed timestamp. -/
theorem storedByte_ledger (names : Names) (a : PhysicalAddress) (byte : Byte) (time : Nat) :
    iprop(storedByte capacity names a byte time ⊢ ledgerByte capacity names a byte) := by
  unfold storedByte ledgerByte
  iintro H
  icases H with ⟨Hbyte, Htime⟩
  iframe Hbyte
  iexists time
  iexact Htime

theorem storedWindow_ledger (names : Names) (a : PhysicalAddress) (n : Nat)
    (word : BitVec bits) (time : Nat) :
    iprop(storedWindow capacity names a n word time ⊢ ledgerWindow capacity names a n word) := by
  unfold storedWindow ledgerWindow
  exact BigSepL.bigSepL_mono_of_forall (storedByte_ledger capacity names _ _ time)

/-- Exact unpinned window postcondition of source `ledger_store_win_ok`. The
stronger `update_window` also retains the receipt and exposed timestamp. -/
theorem update_window_ledger (contracts : Contracts capacity) (names : Names) (eraImage : ByteMap 64)
    (before after : State) (a : PhysicalAddress) (n : Nat) (old new : BitVec bits) (author : Agent)
    (bound : n ≤ 2 ^ 64) (step : WindowTransition before after a n new author) :
    iprop(⊢ heapAt capacity names before.memory -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ledgerWindow capacity names a n old ==∗
      heapAt capacity names after.memory ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      ledgerWindow capacity names a n new) := by
  iintro Hheap Htso Hwindow
  imod update_window capacity contracts names eraImage before after a n old new author bound step
    $$ Hheap Htso Hwindow with ⟨Hheap, Htso, _, Hwindow⟩
  imodintro
  iframe Hheap Htso
  iapply storedWindow_ledger capacity names a n new (before.log.length + 1) $$ Hwindow

theorem storeSpec (contracts : Contracts capacity) : StoreSpec capacity where
  update := update capacity contracts
  window := fun names eraImage before after a n {_} old new author =>
    update_window capacity contracts names eraImage before after a n old new author

end MachCSL.Logic.TsoStore
