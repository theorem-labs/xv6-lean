import Xv6.Fs.RecoveryExamplesDefs
import Xv6.Fs.RecoveryViewProofs

namespace Xv6.Fs.Recovery.Examples

theorem short_header : headerDecode [1] = (1, [0]) := by decide

theorem count_not_clamped : (headerDecode [31]).1 = 31 := by decide

theorem duplicate_first_index (P : Blocks) start (D : BlockMap) :
    (install P start [47, 47] D)[(47 : Int)]? = some (P (SnapshotHome.logSlot start 0)) := by
  simp [install, installStep, List.range_succ]

theorem physical_full changed b : (physical changed b).length = 1024 := by
  unfold physical
  split
  · simp only [header, List.length_append, word32Bytes, List.length_cons, List.length_nil, List.length_replicate]
  · split <;> exact List.length_replicate

theorem header_decode changed : headerDecode (physical changed 2) = (1, [47]) := by
  simp only [physical, ↓reduceIte]
  decide

theorem header_wf changed : HeaderWF (physical changed) coverage 2 := by
  constructor
  · change (headerDecode (physical changed 2)).1 ≤ 30
    rw [header_decode]; decide
  · change (headerDecode (physical changed 2)).2.Nodup
    rw [header_decode]; decide
  · change ∀ b, b ∈ (headerDecode (physical changed 2)).2 → _
    rw [header_decode]
    intro b member
    have same : b = 47 := by simpa using member
    subst b
    constructor
    · decide
    · constructor
      · rw [SnapshotHome.logRegion_mem]; omega
      · decide

theorem slot_value changed :
    view (physical changed) (recover (physical changed) coverage 2) 47 = List.replicate 1024 42 := by
  have found : (headerDecode (physical changed 2)).2[0]? = some 47 := by
    rw [header_decode]; rfl
  have result := recovery_slot (physical changed) (recover (physical changed) coverage 2)
    coverage 2 0 47 rfl (header_wf changed) found
  rw [result]
  change (if (3 : Int) = 2 then _ else if (3 : Int) = 47 ∧ changed = true then _ else _) = _
  rw [if_neg (by decide), if_neg (by omega)]

theorem dirty_changed :
    view (physical true) (recover (physical true) coverage 2) 47 ≠ physical true 47 := by
  rw [slot_value]
  simp only [physical, show (47 : Int) ≠ 2 by decide, ↓reduceIte, and_self]
  intro same
  have heads := congrArg List.head? same
  simp at heads

theorem equal_payload_exception :
    47 ∈ writeSet (physical false) 2 ∧
    view (physical false) (recover (physical false) coverage 2) 47 = physical false 47 := by
  constructor
  · rw [writeSet_mem]
    change (47 : Int) ∈ (headerDecode (physical false 2)).2
    rw [header_decode]; simp
  · rw [slot_value]
    unfold physical
    rw [if_neg (by decide), if_neg (by simp)]

theorem absent_raw_fallback changed :
    view (physical changed) (recover (physical changed) coverage 2) 48 = physical changed 48 := by
  have absent : (recover (physical changed) coverage 2)[(48 : Int)]? = none := by
    have domain := recovery_domain (physical changed) (recover (physical changed) coverage 2)
      coverage 2 rfl (header_wf changed) 48
    have outside : (48 : Int) ∉ SnapshotHome.homeSet coverage 2 := by
      intro member
      have covered := SnapshotHome.homeSet_subset coverage 2 48 member
      simp [coverage] at covered
    cases found : (recover (physical changed) coverage 2)[(48 : Int)]? with
    | none => rfl
    | some bytes => exact False.elim (outside (domain.mp (by simp [found])))
  simp [view, absent]

end Xv6.Fs.Recovery.Examples
