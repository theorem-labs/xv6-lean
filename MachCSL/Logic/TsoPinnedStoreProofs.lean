import MachCSL.Logic.TsoPinnedStoreSpec
import MachCSL.Logic.TsoPinnedStorePure

namespace MachCSL.Logic.TsoPinnedStore
variable {bits : Nat}
open Iris Iris.Std Iris.BI Iris.Algebra MachCSL.Memory MachCSL.Machine TsoStore
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap
variable {GF : BundledGFunctors} (capacity : Capacity GF)

/-- Bulk replacement keeps the original gen_heap metadata authority. All
old timestamp witnesses are collected from existing owned fragments. -/
theorem ledger_update (names : Names) (memory : Tso.AddressMap Byte)
    (timestamps : Tso.AddressMap Tso.TimestampElem) (old new : Tso.AddressMap Byte)
    (oldLength : Nat) (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet)
    (same : SameDomain old new) :
    iprop(⊢ Heap.interp capacity.heap names.heap memory -∗
      Tso.timestampAuth capacity.heap.ledger names.tso.ledger.timestamps (.own 1) timestamps -∗
      pinMap capacity names old (.own 1) floors sets ==∗
      ⌜∀ a, PartialMap.dom new a → PartialMap.dom memory a⌝ ∗
      ⌜∀ a, PartialMap.dom new a → ∃ time, timestamps[a]? = some (time, Tso.payPin (sets a) (floors a))⌝ ∗
      Heap.interp capacity.heap names.heap (memory ∪ new) ∗
      Tso.timestampAuth capacity.heap.ledger names.tso.ledger.timestamps (.own 1)
        (appendTimestamps timestamps new oldLength floors sets) ∗
      storedMap capacity names new (oldLength + 1) floors sets) := by
  letI := capacity.heap.native names.heap
  letI := capacity.heap.ledger.timestamps
  iintro Hheap Htimestamps Hledger
  isimp only [Heap.interp, genHeapInterp, genHeapGS.heapName, genHeapGS.metaName,
    Heap.Capacity.native, Names.heap] at Hheap
  icases Hheap with ⟨%metadata, %metaDomain, Hbytes, Hmetadata⟩
  have exposeCell (a : PhysicalAddress) (byte : Byte) :
      iprop((∃ time : Nat, Tso.physLedgerPin capacity.heap.ledger names.tso.ledger a (.own 1)
        byte time (floors a) (sets a)) ⊢
        Tso.physBytePointsto capacity.heap.ledger names.tso.ledger.bytes a (.own 1) byte ∗
        ∃ e : Tso.TimestampElem,
          Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps (.own 1) a e ∗
          ⌜e.2 = Tso.payPin (sets a) (floors a)⌝) := by
    iintro ⟨%time, Hb, Ht⟩
    iframe Hb
    iexists (time, Tso.payPin (sets a) (floors a))
    iframe Ht
    ipureintro
    rfl
  ihave Hledger := BigSepM.bigSepM_mono (fun {_ _} _ => exposeCell _ _) $$ Hledger
  isimp only [Tso.physBytePointsto, BigSepM.bigSepM_sep_eq] at Hledger
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
  ihave ⟨%oldTimes, %timesDomain, Htimes⟩ := collect_exists
    (fun a e => iprop(Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps (.own 1) a e ∗
      ⌜e.2 = Tso.payPin (sets a) (floors a)⌝)) old $$ Htimes
  isimp only [BigSepM.bigSepM_sep_eq] at Htimes
  icases Htimes with ⟨Htimes, Hpayloads⟩
  ihave %payloads := BigSepM.bigSepM_pure_intro $$ Hpayloads
  ihave %oldSubTimes := (@ghost_map_lookup_big GF PhysicalAddress Tso.TimestampElem Tso.AddressMap
    inferInstance capacity.heap.ledger.timestamps names.tso.ledger.timestamps (.own 1)
    timestamps (.own 1) oldTimes) $$ Htimestamps Htimes
  have registered : ∀ a, PartialMap.dom new a → ∃ time,
      timestamps[a]? = some (time, Tso.payPin (sets a) (floors a)) := by
    intro a present
    have chosen : PartialMap.dom oldTimes a := by rw [timesDomain, same]; exact present
    obtain ⟨e, found⟩ := Option.isSome_iff_exists.mp chosen
    refine ⟨e.1, ?_⟩
    have actual := oldSubTimes a e found
    have shape := payloads a e found
    change get? timestamps a = some (e.1, Tso.payPin (sets a) (floors a))
    rw [← shape]
    exact actual
  have sameTimes : PartialMap.dom oldTimes = PartialMap.dom (storeTimestamps new (oldLength + 1) floors sets) := by
    rw [storeTimestamps_domain, timesDomain]
    exact same
  imod (@ghost_map_update_big GF PhysicalAddress Byte Tso.AddressMap inferInstance
    capacity.heap.ledger.bytes inferInstance names.tso.ledger.bytes memory old new same)
    $$ Hbytes Hcells with ⟨Hbytes, Hcells⟩
  imod (@ghost_map_update_big GF PhysicalAddress Tso.TimestampElem Tso.AddressMap inferInstance
    capacity.heap.ledger.timestamps inferInstance names.tso.ledger.timestamps timestamps
    oldTimes (storeTimestamps new (oldLength + 1) floors sets) sameTimes)
    $$ Htimestamps Htimes with ⟨Htimestamps, Htimes⟩
  isimp only [Union.union, union_eq_std] at Hbytes
  isimp only [Union.union, union_eq_std] at Htimestamps
  imodintro
  isplit
  · ipureintro; exact newDomain
  isplit
  · ipureintro; exact registered
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
  · unfold appendTimestamps
    iexact Htimestamps
  · ihave Htimes := (timestamp_map_bigSep
      (fun a e => Tso.timestampElem capacity.heap.ledger names.tso.ledger.timestamps (.own 1) a e)
      new (oldLength + 1) floors sets).1 $$ Htimes
    unfold storedMap Tso.physLedgerPin Tso.physBytePointsto
    rw [BigSepM.bigSepM_sep_eq, BigSepM.bigSepM_sep_eq]
    iframe Hcells Htimes
    iapply BigSepM.bigSepM_pure.mpr
    ipureintro
    exact newRam

/-- The source ledger store at the complete heap/TSO interpretation. The
successor equations retain every framed payload and update all Nat-agent
view bounds through the existing `avf` interpretation. -/
theorem update (contracts : Contracts capacity) (names : Names) (eraImage : ByteMap 64)
    (before after : State) (old new : Tso.AddressMap Byte) (author : Agent)
    (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet)
    (same : SameDomain old new) (member : ∀ a byte, new[a]? = some byte → byte ∈ sets a)
    (step : Transition before after new author) :
    iprop(⊢ heapAt capacity names before.memory -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      pinMap capacity names old (.own 1) floors sets ==∗
      heapAt capacity names after.memory ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      Tso.History.logElem capacity.history names.tso.logEntries before.log.length
        ⟨FiniteMap.decode new, author⟩ ∗
      storedMap capacity names new (before.log.length + 1) floors sets) := by
  iintro Hheap Htso Hledger
  iunfold heapAt at Hheap
  icases Hheap with ⟨%memory, Hheap, %decoded⟩
  iunfold Tso.Interp.tsoInterpAt at Htso
  icases Htso with ⟨%timestamps, %entries, Htimestamps, %domain, %tie, Hlog, %represented, Hlength, Hviews, %ok⟩
  imod ledger_update capacity names memory timestamps old new before.log.length floors sets same
    $$ Hheap Htimestamps Hledger with ⟨%_, %registered, Hheap, Htimestamps, Hledger⟩
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
    iexists (appendTimestamps timestamps new before.log.length floors sets),
      (PartialMap.insert entries before.log.length ⟨FiniteMap.decode new, author⟩)
    iframe
    ipureintro
    refine ⟨?_, ?_, ?_, transition_memoryOK before after new author step ok.1, step.image.trans ok.2⟩
    · rw [step.memory]
      exact timestampDomain_store before.memory timestamps new before.log.length floors sets domain
    · rw [step.image, step.memory, step.log]
      exact timestampMapOK_store before.image before.memory before.log timestamps new author floors sets tie registered member
    · simpa only [step.log] using represented'
  iframe

/-- Source per-offset floors/sets at the exact finite modular window. -/
theorem window_map
    (Φ : PhysicalAddress → Byte → Nat → Tso.ByteSet → IProp GF)
    (a : PhysicalAddress) (n : Nat) (word : BitVec bits)
    (floors : Nat → Nat) (sets : Nat → Tso.ByteSet)
    (addressFloors : PhysicalAddress → Nat) (addressSets : PhysicalAddress → Tso.ByteSet)
    (bound : n ≤ 2 ^ 64)
    (floorEq : ∀ j, j < n → addressFloors (addressAdd a j) = floors j)
    (setEq : ∀ j, j < n → addressSets (addressAdd a j) = sets j) :
    iprop(([∗map] b ↦ byte ∈ TsoStore.windowMap a n word,
      Φ b byte (addressFloors b) (addressSets b)) ⊣⊢
      [∗list] j ∈ List.range n, Φ (addressAdd a j) (nthByte word j) (floors j) (sets j)) := by
  apply (TsoStore.window_map (fun b byte => Φ b byte (addressFloors b) (addressSets b))
    a n word bound).trans
  apply BiEntails.of_eq
  apply BigSepL.bigSepL_eq
  intro i j present
  have inside : j < n := List.mem_range.mp (List.mem_of_getElem? present)
  rw [floorEq j inside, setEq j inside]

theorem update_window (contracts : Contracts capacity) (names : Names) (image : ByteMap 64)
    (before after : State) (a : PhysicalAddress) (n : Nat) (old new : BitVec bits) (author : Agent)
    (floors : Nat → Nat) (sets : Nat → Tso.ByteSet)
    (addressFloors : PhysicalAddress → Nat) (addressSets : PhysicalAddress → Tso.ByteSet)
    (bound : n ≤ 2 ^ 64)
    (floorEq : ∀ j, j < n → addressFloors (addressAdd a j) = floors j)
    (setEq : ∀ j, j < n → addressSets (addressAdd a j) = sets j)
    (member : ∀ j, j < n → nthByte new j ∈ sets j)
    (step : WindowTransition before after a n new author) :
    iprop(⊢ heapAt capacity names before.memory -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso image before -∗
      pinWindow capacity names a n old (.own 1) floors sets ==∗
      heapAt capacity names after.memory ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso image after ∗
      Tso.History.logElem capacity.history names.tso.logEntries before.log.length
        ⟨snapshot a n new, author⟩ ∗
      storedWindow capacity names a n new (before.log.length + 1) floors sets) := by
  have input : iprop(pinMap capacity names (TsoStore.windowMap a n old) (.own 1) addressFloors addressSets ⊣⊢
      pinWindow capacity names a n old (.own 1) floors sets) :=
    window_map (fun b byte floor allowed => iprop(∃ time : Nat,
      Tso.physLedgerPin capacity.heap.ledger names.tso.ledger b (.own 1) byte time floor allowed))
      a n old floors sets addressFloors addressSets bound floorEq setEq
  have output : iprop(storedMap capacity names (TsoStore.windowMap a n new) (before.log.length + 1)
      addressFloors addressSets ⊣⊢ storedWindow capacity names a n new (before.log.length + 1) floors sets) :=
    window_map (fun b byte floor allowed =>
      Tso.physLedgerPin capacity.heap.ledger names.tso.ledger b (.own 1) byte (before.log.length + 1) floor allowed)
      a n new floors sets addressFloors addressSets bound floorEq setEq
  have allowed : ∀ b byte, (TsoStore.windowMap a n new)[b]? = some byte → byte ∈ addressSets b := by
    intro b byte found
    have mem := LawfulFiniteMap.mem_of_mem_ofList (M := Tso.AddressMap) found
    obtain ⟨j, inside, equal⟩ := List.mem_map.mp mem
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    have hj := List.mem_range.mp inside
    rw [setEq j hj]
    exact member j hj
  iintro Hheap Htso Hwindow
  ihave Hwindow := input.2 $$ Hwindow
  imod update capacity contracts names image before after (TsoStore.windowMap a n old) (TsoStore.windowMap a n new)
    author addressFloors addressSets (windowMap_sameDomain a n old new) allowed
    (windowTransition_as_transition before after a n new author step)
    $$ Hheap Htso Hwindow with ⟨Hheap, Htso, Hreceipt, Hwindow⟩
  imodintro
  isimp only [windowMap_decode] at Hreceipt
  iframe Hheap Htso Hreceipt
  iapply output.1 $$ Hwindow

/-- Hide only the new timestamp, retaining each registered floor and set. -/
theorem storedWindow_pin (names : Names) (a : PhysicalAddress) (n : Nat)
    (word : BitVec bits) (time : Nat) (floors : Nat → Nat) (sets : Nat → Tso.ByteSet) :
    iprop(storedWindow capacity names a n word time floors sets ⊢
      pinWindow capacity names a n word (.own 1) floors sets) := by
  unfold storedWindow pinWindow
  apply BigSepL.bigSepL_mono
  intro i j _
  iintro H
  iexists time
  iexact H

theorem storedMap_pin (names : Names) (memory : Tso.AddressMap Byte) (time : Nat)
    (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet) :
    iprop(storedMap capacity names memory time floors sets ⊢
      pinMap capacity names memory (.own 1) floors sets) := by
  unfold storedMap pinMap Tso.pinMapOwn
  apply BigSepM.bigSepM_mono
  intro a byte _
  iintro H
  iexists time
  iexact H

/-- All assumed subordinate contracts are standard native camera laws. -/
theorem storeSpec (contracts : Contracts capacity) : StoreSpec capacity where
  update := update capacity contracts
  window := fun names image before after a n {_} old new author =>
    update_window capacity contracts names image before after a n old new author

end MachCSL.Logic.TsoPinnedStore
