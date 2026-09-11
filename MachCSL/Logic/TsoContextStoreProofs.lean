import MachCSL.Logic.TsoContextStoreSpec
import MachCSL.Logic.TsoContextProofs
import MachCSL.Logic.TsoStoreLink

namespace MachCSL.Logic.TsoContextStore
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Machine TsoContext
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap

theorem mem_registerEntries (old : Tso.History.DirtySet) (time : Nat)
    (entries : List (PhysicalAddress × Byte)) (key : Tso.History.DirtyKey) :
    key ∈ registerEntries old time entries ↔
      key ∈ old ∨ (key.1 = time ∧ key.2 ∈ entries.map Prod.fst) := by
  induction entries with
  | nil => simp [registerEntries]
  | cons entry rest ih =>
    rcases key with ⟨stamp, address⟩
    simp only [registerEntries, mem_union, mem_singleton, ih, Prod.mk.injEq,
      List.map_cons, List.mem_cons]
    simp only [and_or_left, or_assoc, or_left_comm, or_comm]

theorem mem_registerDirty (old : Tso.History.DirtySet) (time : Nat)
    (new : Tso.AddressMap Byte) (key : Tso.History.DirtyKey) :
    key ∈ registerDirty old time new ↔
      key ∈ old ∨ (key.1 = time ∧ PartialMap.dom new key.2) := by
  rw [registerDirty, mem_registerEntries]
  have domain : key.2 ∈ (FiniteMap.toList new).map Prod.fst ↔ PartialMap.dom new key.2 := by
    constructor
    · intro h
      obtain ⟨⟨a, byte⟩, member, equal⟩ := List.mem_map.mp h
      dsimp only at equal
      subst a
      have lookup := (LawfulFiniteMap.toList_get (m := new)).mp member
      simp [PartialMap.dom, lookup]
    · intro h
      obtain ⟨byte, lookup⟩ := Option.isSome_iff_exists.mp h
      exact List.mem_map.mpr ⟨(key.2, byte), (LawfulFiniteMap.toList_get (m := new)).mpr lookup, rfl⟩
  rw [domain]

variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem register_entries γ (old : Tso.History.DirtySet) time entries :
    iprop(⊢ Tso.History.dsetAuth capacity.history γ 1 old ==∗
      Tso.History.dsetAuth capacity.history γ 1 (registerEntries old time entries) ∗
      [∗list] entry ∈ entries, Tso.History.dsetIn capacity.history γ (time, entry.1)) := by
  induction entries with
  | nil =>
    iintro Hd
    imodintro
    simp only [registerEntries]
    iframe Hd
    exact BigSepL.bigSepL_nil_intro
  | cons entry rest ih =>
    iintro Hd
    imod ih $$ Hd with ⟨Hd, Htail⟩
    imod Tso.History.dset_insert capacity.history γ (registerEntries old time rest) (time, entry.1)
      $$ Hd with ⟨Hd, Hhead⟩
    imodintro
    simp only [registerEntries]
    iframe Hd Hhead Htail

theorem register_dirty γ old time new :
    iprop(⊢ Tso.History.dsetAuth capacity.history γ 1 old ==∗
      Tso.History.dsetAuth capacity.history γ 1 (registerDirty old time new) ∗
      [∗map] a ↦ _byte ∈ new, Tso.History.dsetIn capacity.history γ (time, a)) := by
  rw [BigSepM.bigSepM_toList.to_eq]
  exact register_entries capacity γ old time (FiniteMap.toList new)

/-- Forget only a byte's visibility justification; retain its full value and
timestamp ownership. The old dirty authority is not changed. -/
theorem map_ledger names ξ old :
    iprop(physMap capacity names ξ old ⊢ TsoStore.ledgerMap capacity names old) := by
  unfold physMap TsoStore.ledgerMap
  apply BigSepM.bigSepM_mono
  intro a byte _lookup
  unfold physPointsto TsoStore.ledgerByte
  iintro ⟨%time, Hb, Ht, _⟩
  iframe Hb
  iexists time
  iexact Ht

theorem watermark_bound (names : Names) eraImage g W :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      Tso.Views.llb capacity.views names.tso.logLength W -∗ ⌜W ≤ g.log.length⌝) := by
  unfold Tso.Interp.tsoInterpAt
  iintro ⟨%_timestamps, %_entries, _, _, _, _, _, Hlen, _, _⟩ HW
  iapply Tso.Views.llb_valid capacity.views names.tso.logLength (.own 1) g.log.length W $$ Hlen HW

theorem current_watermark (names : Names) eraImage g :
    iprop(⊢ Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage g -∗
      Tso.Views.llb capacity.views names.tso.logLength g.log.length) := by
  unfold Tso.Interp.tsoInterpAt
  iintro ⟨%_timestamps, %_entries, _, _, _, _, _, Hlen, _, _⟩
  ihave ⟨_, Hlb⟩ := Tso.Views.llb_get capacity.views names.tso.logLength (.own 1) g.log.length $$ Hlen
  iexact Hlb

/-- Every new dirty key is justified by the one actual appended message;
every old justification is retained without changing the context bound. -/
theorem register_justifications (names : Names) cpu B D i (new : Tso.AddressMap Byte) :
    iprop(⊢ ([∗set] key ∈ D, Tso.History.dirtyOK capacity.history names.tso.logEntries (hartAgent cpu) B key) -∗
      Tso.History.logElem capacity.history names.tso.logEntries i ⟨FiniteMap.decode new, hartAgent cpu⟩ -∗
      [∗set] key ∈ registerDirty D (i + 1) new,
        Tso.History.dirtyOK capacity.history names.tso.logEntries (hartAgent cpu) B key) := by
  iintro #Hold #Hmessage
  iapply BigSepS.bigSepS_forall.mpr
  iintro %key %member
  rcases (mem_registerDirty D (i + 1) new key).mp member with old | ⟨time, _⟩
  · iapply BigSepS.bigSepS_elem_of old $$ Hold
  · iapply Tso.History.dirtyOK_author capacity.history names.tso.logEntries (hartAgent cpu) B key i
      ⟨FiniteMap.decode new, hartAgent cpu⟩ time rfl $$ Hmessage

theorem stored_context names ξ time new :
    iprop(TsoStore.storedMap capacity names new time ∗
      ([∗map] a ↦ _byte ∈ new, Tso.History.dsetIn capacity.history ξ.dirty (time, a)) ⊢
      physMap capacity names ξ new) := by
  unfold TsoStore.storedMap physMap
  rw [BigSepM.bigSepM_sep_eq_symm]
  apply BigSepM.bigSepM_mono
  intro a byte _lookup
  unfold TsoStore.storedByte physPointsto
  iintro ⟨⟨Hb, Ht⟩, Hd⟩
  iexists time
  iframe Hb Ht
  iright
  iexact Hd

/-- Exact registered physical store gate. The full-map native payer appends
one message, while registration updates only the context's dirty-set ghost. -/
theorem store names cpu ξ eraImage before after old new
    (same : TsoStore.SameDomain old new)
    (step : TsoStore.Transition before after new (hartAgent cpu)) :
    iprop(⊢ TsoContext.heapAt capacity names before -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ownContext capacity names cpu ξ -∗ physMap capacity names ξ old ==∗
      TsoContext.heapAt capacity names after ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      ownContext capacity names cpu ξ ∗ physMap capacity names ξ new) := by
  iintro Hheap Htso Hrun Hold
  unfold ownContext ctxAt
  icases Hrun with ⟨%B, %K, %W, %D, ⟨Hb, Hd⟩, #Hview, %bound, #HW, %watermark, #Hoks⟩
  ihave %Wbound := watermark_bound capacity names eraImage before W $$ Htso HW
  ihave Hledger := map_ledger capacity names ξ old $$ Hold
  have gate := (TsoStore.nativeStoreSpec capacity).update names eraImage before after old new (hartAgent cpu) same step
  rw [show TsoStore.heapAt capacity names before.memory = TsoContext.heapAt capacity names before from rfl,
    show TsoStore.heapAt capacity names after.memory = TsoContext.heapAt capacity names after from rfl] at gate
  imod gate $$ Hheap Htso Hledger with ⟨Hheap, Htso, #Hmessage, Hstored⟩
  imod register_dirty capacity ξ.dirty D (before.log.length + 1) new $$ Hd with ⟨Hd, Hmembers⟩
  ihave #HnewW := current_watermark capacity names eraImage after $$ Htso
  ihave #HnewOks := register_justifications capacity names cpu B D before.log.length new $$ Hoks Hmessage
  have length : after.log.length = before.log.length + 1 := by simp [step.log]
  imodintro
  iframe Hheap Htso
  isplitl [Hb Hd]
  · iexists B, K, after.log.length, registerDirty D (before.log.length + 1) new
    iframe Hb Hd Hview HnewW HnewOks
    ipureintro
    refine ⟨bound, ?_⟩
    intro key member
    rcases (mem_registerDirty D (before.log.length + 1) new key).mp member with old | ⟨time, _⟩
    · have := watermark key old
      omega
    · omega
  · iapply stored_context capacity names ξ (before.log.length + 1) new $$ [$Hstored $Hmembers]

/-- Source ordinary stores keep all CPU views unchanged. The post-view bound
is derived from the actual pre-state interpretation, not assumed by clients. -/
theorem ordinary names cpu ξ eraImage before after old new
    (same : TsoStore.SameDomain old new) (step : OrdinaryTransition before after new cpu) :
    iprop(⊢ TsoContext.heapAt capacity names before -∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage before -∗
      ownContext capacity names cpu ξ -∗ physMap capacity names ξ old ==∗
      TsoContext.heapAt capacity names after ∗
      Tso.Interp.tsoInterpAt capacity.tso names.tso eraImage after ∗
      ownContext capacity names cpu ξ ∗ physMap capacity names ξ new) := by
  iintro Hheap Htso Hrun Hold
  ihave %ok := Tso.Interp.tsoInterpAt_memoryOK capacity.tso names.tso eraImage before $$ Htso
  have transition : TsoStore.Transition before after new (hartAgent cpu) := by
    refine ⟨step.image, step.log, step.memory, ?_, ?_⟩
    · intro cpu
      rw [step.views]
      exact Nat.le_refl _
    · intro cpu
      rw [step.views, step.log, List.length_append, List.length_singleton]
      have bound := ok.2.1 cpu
      omega
  iapply store capacity names cpu ξ eraImage before after old new same transition $$ Hheap Htso Hrun Hold

theorem actual : Spec capacity := ⟨store capacity, ordinary capacity⟩

end MachCSL.Logic.TsoContextStore
