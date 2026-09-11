import MachCSL.Logic.TsoAppendDefs

/-! Untouched-address append laws from TsoMemPa.v. These preserve all four
source payload arms; a write at another address cannot discard their claims. -/
namespace MachCSL.Logic.Tso
open MachCSL.Memory

/-- A newly appended message that misses an address cannot be a witnessed
message touching that address. Thus every such lookup is in the old log. -/
theorem append_touch_lookup (log : WriteLog 64) (msg : Message 64) (a : PhysicalAddress)
    (miss : msgByte msg a = none) (i : Nat) (m : Message 64)
    (lookup : (log ++ [msg])[i]? = some m) (touch : (msgByte m a).isSome) :
    log[i]? = some m := by
  by_cases old : i < log.length
  · rwa [List.getElem?_append_left old] at lookup
  · have bound := (List.getElem?_eq_some_iff.mp lookup).1
    have eq : i = log.length := by simp only [List.length_append, List.length_singleton] at bound; omega
    subst i
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero] at lookup
    cases Option.some.inj lookup
    simp only [miss, Option.isSome_none] at touch
    contradiction

theorem ownLastFloor_append_frame (log : WriteLog 64) (msg : Message 64)
    (bound : Nat) (h : Agent) (a : PhysicalAddress) (t : Nat)
    (floor : OwnLastFloor log bound h a t) (miss : msgByte msg a = none) :
    OwnLastFloor (log ++ [msg]) bound h a t := by
  intro i m above lookup author touch
  exact floor i m above (append_touch_lookup log msg a miss i m lookup touch) author touch

theorem windowOK_append_frame (image : ByteMap 64) (log : WriteLog 64)
    (msg : Message 64) (a : PhysicalAddress) (w : Window)
    (ok : WindowOK image log a w) (miss : msgByte msg a = none) :
    WindowOK image (log ++ [msg]) a w := by
  obtain ⟨addr, index, words, domain, lo, clear, own⟩ := ok
  refine ⟨addr, index, ?_, domain, ?_, ?_, ?_⟩
  · intro i m above lookup touch
    exact words i m above (append_touch_lookup log msg a miss i m lookup touch) touch
  · simp only [List.length_append, List.length_singleton]; omega
  · intro k hk
    rw [logByte_append_below image log msg w.lo _ lo]
    exact clear k hk
  · intro h t found
    obtain ⟨lower, upper, visible, value, floor⟩ := own h t found
    refine ⟨lower, ?_, ?_, ?_, ownLastFloor_append_frame log msg w.lo h a t floor miss⟩
    · simp only [List.length_append, List.length_singleton]; omega
    · intro view above
      rw [visible_append h view log msg t upper]
      exact visible view above
    · rw [logByte_append_below image log msg t a upper]
      exact value

theorem releaseOK_append_frame (image : ByteMap 64) (log : WriteLog 64)
    (msg : Message 64) (a : PhysicalAddress) (r : Release)
    (ok : ReleaseOK image log a r) (miss : msgByte msg a = none) :
    ReleaseOK image (log ++ [msg]) a r := by
  obtain ⟨addr, index, lo, history, represented, domain, floor⟩ := ok
  refine ⟨addr, index, ?_, ?_, ?_, domain, ?_⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · intro i m above lookup touch
    exact history i m above (append_touch_lookup log msg a miss i m lookup touch) touch
  · intro q f member
    obtain ⟨above, i, m, time, lookup, author, word⟩ := represented q f member
    refine ⟨above, i, m, time, ?_, author, word⟩
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp lookup).1]
    exact lookup
  · intro k hk
    obtain ⟨lower, value, empty⟩ := floor k hk
    refine ⟨lower, ?_, ?_⟩
    · rw [logByte_append_below image log msg (r.floor k) _ (by omega)]
      exact value
    · intro t above below
      rw [logByte_append_below image log msg t _ (by omega)]
      exact empty t above below

theorem wordPinOK_append_frame (image : ByteMap 64) (log : WriteLog 64)
    (msg : Message 64) (a : PhysicalAddress) (w : WordPin)
    (ok : WordPinOK image log a w) (miss : msgByte msg a = none) :
    WordPinOK image (log ++ [msg]) a w := by
  obtain ⟨addr, index, positive, words, lo, f, member, value⟩ := ok
  refine ⟨addr, index, positive, ?_, ?_, f, member, ?_⟩
  · intro i m above lookup touch
    exact words i m above (append_touch_lookup log msg a miss i m lookup touch) touch
  · simp only [List.length_append, List.length_singleton]; omega
  · intro k hk
    rw [logByte_append_below image log msg w.lo _ lo]
    exact value k hk

/-- Pointwise memory equality is the complete untouched-byte obligation. The
payload itself is preserved, including its window/history/predicate functions. -/
theorem timestampOK_append_frame (image memory memory' : ByteMap 64) (log : WriteLog 64)
    (msg : Message 64) (a : PhysicalAddress) (e : TimestampElem)
    (ok : TimestampOK image memory log a e) (miss : msgByte msg a = none)
    (same : memory' a = memory a) : TimestampOK image memory' (log ++ [msg]) a e := by
  obtain ⟨⟨byte, value, latest⟩, pin, win, rel, pinw⟩ := ok
  refine ⟨⟨byte, same.trans value, latest_append_frame image log msg a e.1 byte miss latest⟩,
    ?_, ?_, ?_, ?_⟩
  · intro allowed bound found
    exact pinOK_append_frame (pin allowed bound found) miss
  · intro w found
    exact windowOK_append_frame image log msg a w (win w found) miss
  · intro r found
    exact releaseOK_append_frame image log msg a r (rel r found) miss
  · intro w found
    exact wordPinOK_append_frame image log msg a w (pinw w found) miss

theorem appendTimestamps_lookup (old : AddressMap TimestampElem) (newBytes : AddressMap Byte)
    (oldLength : Nat) (a : PhysicalAddress) :
    (appendTimestamps old newBytes oldLength)[a]? =
      (newBytes[a]?.map (fun _ => (oldLength + 1, payNone))).or old[a]? := by
  simp only [appendTimestamps, storeTimestamps, Std.ExtTreeMap.getElem?_union,
    Std.ExtTreeMap.getElem?_map]

/-- All touched bytes receive the new timestamp and no payload. Every
untouched byte retains all four payload arms, not merely its current value. -/
theorem timestampMapOK_store (image memory : ByteMap 64) (log : WriteLog 64)
    (old : AddressMap TimestampElem) (newBytes : AddressMap Byte) (author : Agent)
    (tie : TimestampMapOK image memory log old) :
    TimestampMapOK image (overlay (FiniteMap.decode newBytes) memory)
      (log ++ [⟨FiniteMap.decode newBytes, author⟩])
      (appendTimestamps old newBytes log.length) := by
  intro a e lookup
  rw [appendTimestamps_lookup] at lookup
  cases written : newBytes[a]? with
  | some byte =>
    simp only [written, Option.map_some, Option.some_or] at lookup
    cases Option.some.inj lookup
    apply timestampOK_unpinned (byte := byte)
    · simp only [overlay, FiniteMap.decode, written, Option.some_or]
    · apply latest_append_new
      exact written
  | none =>
    simp only [written, Option.map_none, Option.none_or] at lookup
    apply timestampOK_append_frame image memory _ log _ a e (tie a e lookup)
    · exact written
    · simp only [overlay, FiniteMap.decode, written, Option.none_or]

theorem timestampDomain_store (memory : ByteMap 64) (old : AddressMap TimestampElem)
    (newBytes : AddressMap Byte) (oldLength : Nat)
    (domain : Interp.TimestampDomain old memory) :
    Interp.TimestampDomain (appendTimestamps old newBytes oldLength)
      (overlay (FiniteMap.decode newBytes) memory) := by
  intro a
  rw [appendTimestamps_lookup]
  cases written : newBytes[a]? with
  | some byte =>
    simp [Domain, overlay, FiniteMap.decode, written]
  | none =>
    simpa only [Option.map_none, Option.none_or, Domain, overlay, FiniteMap.decode, written] using domain a

end MachCSL.Logic.Tso
