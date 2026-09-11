import MachCSL.Logic.ContextPinMintSpec
import MachCSL.Logic.TsoInterpProofs

namespace MachCSL.Logic.ContextPinMint
open Iris Iris.Std Iris.BI MachCSL.Memory MachCSL.Machine

open Iris.Std.LawfulPartialMap

theorem fold_max_ge (xs : List Nat) (x : Nat) (member : x ∈ xs) :
    x ≤ xs.foldr Nat.max 0 := by
  induction xs with
  | nil => simp at member
  | cons y ys ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

theorem ownPub_ge (h : Agent) (log : WriteLog 64) (i : Nat) (msg : Message 64)
    (lookup : log[i]? = some msg) (author : msg.author = h) : i + 1 ≤ ownPub h log := by
  apply fold_max_ge
  have member : (msg, i) ∈ log.zipIdx :=
    List.mem_of_getElem? (i := i) (by simp [List.getElem?_zipIdx, lookup])
  exact List.mem_map.mpr ⟨(msg, i), member, by simp [author]⟩

theorem pin_insert_domain (timestamps : Tso.AddressMap Tso.TimestampElem)
    (memory : ByteMap 64) (a : PhysicalAddress) (e : Tso.TimestampElem)
    (domain : Tso.Interp.TimestampDomain timestamps memory)
    (present : Domain memory a) :
    Tso.Interp.TimestampDomain (PartialMap.insert timestamps a e) memory := by
  intro b
  change (get? (PartialMap.insert timestamps a e) b).isSome ↔ _
  rw [get?_insert]
  split
  · subst b; simpa using present
  · exact domain b

theorem pin_insert_ok (timestamps : Tso.AddressMap Tso.TimestampElem)
    (image memory : ByteMap 64) (log : WriteLog 64) a byte time bound allowed
    (ok : Tso.TimestampMapOK image memory log timestamps)
    (lookup : memory a = some byte) (latest : Latest image log a time byte)
    (le : time ≤ bound) (member : byte ∈ allowed) :
    Tso.TimestampMapOK image memory log
      (PartialMap.insert timestamps a (time, Tso.payPin allowed bound)) := by
  intro b e he
  change get? (PartialMap.insert timestamps a (time, Tso.payPin allowed bound)) b = some e at he
  rw [get?_insert] at he
  split at he
  · subst b
    cases Option.some.inj he
    refine ⟨⟨byte, lookup, latest⟩, ?_, ?_, ?_, ?_⟩
    · intro allowed' bound' hp
      have eqs : allowed = allowed' ∧ bound = bound' := by
        simpa [Tso.payPin] using hp
      obtain ⟨rfl, rfl⟩ := eqs
      exact Tso.pinOK_mint latest le member
    all_goals simp [Tso.payPin]
  · exact ok b e he

end MachCSL.Logic.ContextPinMint
