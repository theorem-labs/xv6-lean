import MachCSL.Logic.TsoInterpSpec
import MachCSL.Logic.TsoOwnership
import MachCSL.Logic.TsoViewsProofs
import MachCSL.Logic.TsoHistoryProofs

namespace MachCSL.Logic.Tso.Interp
open MachCSL.Memory MachCSL.Machine Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI

theorem avf_hart (g : State) (cpu : CPU) : avf g (hartAgent cpu) = g.views cpu := by
  simp [avf, hartAgent, cpu.isLt]

theorem avf_disk (g : State) : avf g diskAgent = g.log.length := by
  simp [avf, diskAgent]

theorem avf_device (g : State) (h : Agent) (bound : 8 ≤ h) :
    avf g h = g.log.length := by
  simp [avf, Nat.not_lt.mpr bound]

theorem avf_bound (g : State) (ok : MemoryOK g) (h : Agent) :
    avf g h ≤ g.log.length := by
  unfold avf
  split
  · exact ok.2.1 _
  · exact Nat.le_refl _

theorem avf_boot (image : BootImage) (g : State) (facts : BootFacts image g) :
    avf g = fun _ => 0 := by
  obtain ⟨_, _, _, _, _, _, _, log, _, views⟩ := facts
  funext h
  simp [avf, log, views]

/-- Explicit extensional-domain equality, matching the source finite-map domains. -/
theorem timestampDomain_iff_domainEq (timestamps : AddressMap TimestampElem)
    (memory : ByteMap 64) : TimestampDomain timestamps memory ↔
      (fun a => ∃ e, timestamps[a]? = some e) = Domain memory := by
  constructor
  · intro h
    funext a
    apply propext
    have ha := h a
    change timestamps[a]?.isSome ↔ Domain memory a at ha
    cases hm : timestamps[a]? <;> simpa [hm] using ha
  · intro h a
    have ha := congrFun h a
    rw [← ha]
    cases timestamps[a]? <;> simp

theorem bootTimestamps_lookup (memory : AddressMap Byte) (a : PhysicalAddress) :
    (bootTimestamps memory)[a]? = memory[a]?.map (fun _ => (0, payNone)) := by
  simp [bootTimestamps]

theorem bootTimestamps_domain (memory : AddressMap Byte) :
    TimestampDomain (bootTimestamps memory) (FiniteMap.decode memory) := by
  intro a
  rw [bootTimestamps_lookup]
  simp only [FiniteMap.decode, Domain]
  cases memory[a]? <;> simp

theorem bootTimestamps_ok (image : BootImage) (g : State) (memory : AddressMap Byte)
    (facts : BootFacts image g) (rep : FiniteMap.decode memory = g.memory) :
    TimestampMapOK g.image g.memory g.log (bootTimestamps memory) := by
  obtain ⟨_, _, _, _, _, _, _, log, initial, _⟩ := facts
  intro a e present
  rw [bootTimestamps_lookup] at present
  cases hm : memory[a]? with
  | none => simp [hm] at present
  | some byte =>
    have he : e = (0, payNone) := by simpa [hm] using present.symm
    subst e
    have hv : g.memory a = some byte := by
      rw [← rep]
      exact hm
    apply timestampOK_unpinned hv
    rw [log, initial]
    constructor
    · exact hv
    · intro t positive
      cases t with
      | zero => omega
      | succ t => rfl

variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem tsoInterpAt_image (names : EraNames) (eraImage : ByteMap 64) (g : State) :
    iprop(⊢ tsoInterpAt capacity names eraImage g -∗ ⌜g.image = eraImage⌝) := by
  unfold tsoInterpAt
  iintro ⟨%timestamps, %entries, _, _, _, _, _, _, _, %ok⟩
  ipureintro
  exact ok.2

theorem tsoInterpAt_memoryOK (names : EraNames) (eraImage : ByteMap 64) (g : State) :
    iprop(⊢ tsoInterpAt capacity names eraImage g -∗ ⌜MemoryOK g⌝) := by
  unfold tsoInterpAt
  iintro ⟨%timestamps, %entries, _, _, _, _, _, _, _, %ok⟩
  ipureintro
  exact ok.1

theorem tsoInterpAt_timestamp_valid (names : EraNames) (eraImage : ByteMap 64) (g : State)
    (a : PhysicalAddress) (dq : DFrac) (e : TimestampElem) :
    iprop(⊢ tsoInterpAt capacity names eraImage g -∗
      timestampElem capacity.ledger names.ledger.timestamps dq a e -∗
      ⌜TimestampOK g.image g.memory g.log a e⌝) := by
  unfold tsoInterpAt
  iintro ⟨%timestamps, %entries, Hts, _, %tie, _, _, _, _, _⟩ He
  ihave %lookup := timestamp_lookup capacity.ledger names.ledger.timestamps
    (.own 1) timestamps a dq e $$ Hts He
  ipureintro
  exact tie a e lookup

/-- Allocate the actual boot TSO conjunct from an explicit finite representation.
Every full client byte and timestamp fragment is returned, together with the
byte authority which belongs to the adjacent source gen_heap conjunct. -/
theorem tsoInterpAt_alloc (image : BootImage) (g : State) (memory : AddressMap Byte)
    (facts : BootFacts image g) (rep : FiniteMap.decode memory = g.memory) :
    iprop(⊢ |==> ∃ names : EraNames,
      tsoInterpAt capacity names g.image g ∗
      byteInterpAt capacity names memory g ∗ bootClients capacity names memory) := by
  have hlog : g.log = [] := facts.2.2.2.2.2.2.2.1
  have hdomain : TimestampDomain (bootTimestamps memory) g.memory := by
    rw [← rep]
    exact bootTimestamps_domain memory
  have htie := bootTimestamps_ok image g memory facts rep
  have hrep : History.LogRep ∅ g.log := by
    intro i
    simp [hlog, PartialMap.get?]
  have hok : MemoryOK g ∧ g.image = g.image := ⟨boot_memory_ok image g facts, rfl⟩
  imod ledger_alloc capacity.ledger memory (bootTimestamps memory) with
    ⟨%ledgerNames, Hb, Hts, Hbytes, Htimestamps⟩
  imod History.log_alloc capacity.history with ⟨%γlog, Hlog⟩
  imod Views.natAuth_alloc capacity.views 0 with ⟨%γlen, Hlen, Hreceipt⟩
  imod Views.viewAuth_alloc capacity.views (avf g) with ⟨%γview, Hview⟩
  imodintro
  iexists (EraNames.mk ledgerNames γlog γlen γview)
  isplitl [Hts Hlog Hlen Hview]
  · unfold tsoInterpAt
    iexists (bootTimestamps memory), (∅ : History.LogMap (Message 64))
    rw [hlog]
    iframe
    ipureintro
    exact ⟨hdomain, by simpa [hlog] using htie, by simpa [hlog] using hrep, hok⟩
  · unfold byteInterpAt bootClients
    iframe
    ipureintro
    exact rep

/-- Logical finite-domain witness. This corollary never evaluates a 2^64-key
encoding; clients with an efficient support map should use `tsoInterpAt_alloc`. -/
theorem tsoInterpAt_alloc_finite (image : BootImage) (g : State)
    (facts : BootFacts image g) :
    iprop(⊢ |==> ∃ (names : EraNames) (memory : AddressMap Byte),
      tsoInterpAt capacity names g.image g ∗
      byteInterpAt capacity names memory g ∗ bootClients capacity names memory) := by
  imod tsoInterpAt_alloc capacity image g (FiniteMap.encodeAll g.memory)
    facts (FiniteMap.decode_encodeAll g.memory) with ⟨%names, H⟩
  imodintro
  iexists names, (FiniteMap.encodeAll g.memory)
  iexact H

theorem interpSpec : InterpSpec capacity :=
  ⟨tsoInterpAt_image capacity, tsoInterpAt_memoryOK capacity,
    tsoInterpAt_timestamp_valid capacity, tsoInterpAt_alloc capacity⟩

theorem registryInterpSpec : InterpSpec registryCapacity := interpSpec registryCapacity

end MachCSL.Logic.Tso.Interp
