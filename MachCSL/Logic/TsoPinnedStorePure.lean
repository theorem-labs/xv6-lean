import MachCSL.Logic.TsoPinnedStoreDefs
import MachCSL.Logic.TsoStoreProofs

namespace MachCSL.Logic.TsoPinnedStore
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Machine
open Iris.Std.PartialMap Iris.Std.LawfulPartialMap

theorem storeTimestamps_lookup (new : Tso.AddressMap Byte) (time : Nat)
    (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet) (a : PhysicalAddress) :
    (storeTimestamps new time floors sets)[a]? =
      new[a]?.map (fun _ => (time, Tso.payPin (sets a) (floors a))) := by
  simp [storeTimestamps]

theorem storeTimestamps_domain (new : Tso.AddressMap Byte) (time : Nat)
    (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet) :
    PartialMap.dom (storeTimestamps new time floors sets) = PartialMap.dom new := by
  funext a
  apply propext
  change ((storeTimestamps new time floors sets)[a]?).isSome ↔ (new[a]?).isSome
  rw [storeTimestamps_lookup]
  simp

theorem storeTimestamps_empty (time : Nat) (floors : PhysicalAddress → Nat)
    (sets : PhysicalAddress → Tso.ByteSet) :
    storeTimestamps ∅ time floors sets = ∅ := by
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro a
  simp [storeTimestamps_lookup]

theorem storeTimestamps_insert (new : Tso.AddressMap Byte) (time : Nat)
    (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet)
    (a : PhysicalAddress) (byte : Byte) :
    storeTimestamps (PartialMap.insert new a byte) time floors sets =
      PartialMap.insert (storeTimestamps new time floors sets) a (time, Tso.payPin (sets a) (floors a)) := by
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro b
  rw [storeTimestamps_lookup]
  change (get? (PartialMap.insert new a byte) b).map _ = get? (PartialMap.insert (storeTimestamps new time floors sets) a
    (time, Tso.payPin (sets a) (floors a))) b
  rw [get?_insert, get?_insert]
  by_cases equal : a = b
  · subst b; simp
  · simp only [equal, ↓reduceIte]
    exact (storeTimestamps_lookup new time floors sets b).symm

theorem appendTimestamps_lookup (old : Tso.AddressMap Tso.TimestampElem) (new : Tso.AddressMap Byte)
    (oldLength : Nat) (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet)
    (a : PhysicalAddress) :
    (appendTimestamps old new oldLength floors sets)[a]? =
      (new[a]?.map (fun _ => (oldLength + 1, Tso.payPin (sets a) (floors a)))).or old[a]? := by
  simp only [appendTimestamps, _root_.Std.ExtTreeMap.getElem?_union, storeTimestamps_lookup]

theorem appendTimestamps_untouched (old : Tso.AddressMap Tso.TimestampElem) (new : Tso.AddressMap Byte)
    (oldLength : Nat) (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet)
    (a : PhysicalAddress) (absent : new[a]? = none) :
    (appendTimestamps old new oldLength floors sets)[a]? = old[a]? := by
  simp only [appendTimestamps_lookup, absent, Option.map_none, Option.none_or]

theorem timestampMapOK_store (image memory : ByteMap 64) (log : WriteLog 64)
    (old : Tso.AddressMap Tso.TimestampElem) (new : Tso.AddressMap Byte) (author : Agent)
    (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet)
    (tie : Tso.TimestampMapOK image memory log old)
    (registered : ∀ a, PartialMap.dom new a → ∃ time, old[a]? = some (time, Tso.payPin (sets a) (floors a)))
    (member : ∀ a byte, new[a]? = some byte → byte ∈ sets a) :
    Tso.TimestampMapOK image (overlay (FiniteMap.decode new) memory)
      (log ++ [⟨FiniteMap.decode new, author⟩]) (appendTimestamps old new log.length floors sets) := by
  intro a e lookup
  rw [appendTimestamps_lookup] at lookup
  cases written : new[a]? with
  | some byte =>
    simp only [written, Option.map_some, Option.some_or] at lookup
    cases Option.some.inj lookup
    obtain ⟨time, oldLookup⟩ := registered a (by change (new[a]?).isSome = true; rw [written]; rfl)
    have pin := Tso.timestampOK_pin (tie a _ oldLookup) rfl
    refine ⟨⟨byte, ?_, latest_append_new image log _ a byte written⟩, ?_, ?_, ?_, ?_⟩
    · simp only [overlay, FiniteMap.decode, written, Option.some_or]
    · intro allowed bound found
      have equal : sets a = allowed ∧ floors a = bound := by simpa [Tso.payPin] using found
      rcases equal with ⟨rfl, rfl⟩
      exact Tso.pinOK_append pin (Or.inr ⟨byte, written, member a byte written⟩)
    · simp [Tso.payPin]
    · simp [Tso.payPin]
    · simp [Tso.payPin]
  | none =>
    simp only [written, Option.map_none, Option.none_or] at lookup
    apply Tso.timestampOK_append_frame image memory _ log _ a e (tie a e lookup)
    · exact written
    · simp only [overlay, FiniteMap.decode, written, Option.none_or]

theorem timestampDomain_store (memory : ByteMap 64) (old : Tso.AddressMap Tso.TimestampElem)
    (new : Tso.AddressMap Byte) (oldLength : Nat)
    (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet)
    (domain : Tso.Interp.TimestampDomain old memory) :
    Tso.Interp.TimestampDomain (appendTimestamps old new oldLength floors sets)
      (overlay (FiniteMap.decode new) memory) := by
  intro a
  rw [appendTimestamps_lookup]
  cases written : new[a]? with
  | some byte => simp [Domain, overlay, FiniteMap.decode, written]
  | none =>
    simpa only [Option.map_none, Option.none_or, Domain, overlay, FiniteMap.decode, written] using domain a

/-- Key-dependent map transport, proved over the existing finite-map API. -/
theorem timestamp_map_bigSep {GF : BundledGFunctors}
    (Φ : PhysicalAddress → Tso.TimestampElem → IProp GF) (new : Tso.AddressMap Byte) (time : Nat)
    (floors : PhysicalAddress → Nat) (sets : PhysicalAddress → Tso.ByteSet) :
    iprop(([∗map] a ↦ e ∈ storeTimestamps new time floors sets, Φ a e) ⊣⊢
      [∗map] a ↦ _byte ∈ new, Φ a (time, Tso.payPin (sets a) (floors a))) := by
  induction new using LawfulFiniteMap.induction_on with
  | hemp => rw [storeTimestamps_empty]; exact BigSepM.bigSepM_empty.trans BigSepM.bigSepM_empty.symm
  | hins a byte new absent ih =>
    have missing : get? (storeTimestamps new time floors sets) a = none := by
      change (storeTimestamps new time floors sets)[a]? = none
      rw [storeTimestamps_lookup]
      change (get? new a).map _ = _
      rw [absent]; rfl
    rw [storeTimestamps_insert, (BigSepM.bigSepM_insert missing).to_eq,
      (BigSepM.bigSepM_insert absent).to_eq, ih.to_eq]
    exact .rfl

end MachCSL.Logic.TsoPinnedStore
