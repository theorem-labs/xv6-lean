import Xv6.Fs.DurableNodeSpec
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace Xv6.Fs.DurableNode

variable {n : Node} {inum : Int}

theorem repr_of_local (h : Local inum n) : Repr n :=
  ⟨h.record, h.entryLength, h.indirectZero, h.domain, h.top⟩

theorem data_lookup (n : Node) (k : Nat) (bytes : List (BitVec 8))
    (h : n.blocks[k]? = some bytes) : n.data k = bytes := by simp only [Node.data, h, Option.getD_some]

theorem data_missing (n : Node) (k : Nat) (h : n.blocks[k]? = none) :
    n.data k = List.replicate 1024 0 := by simp only [Node.data, h, Option.getD_none]

theorem local_read (h : Local inum n) (k : Nat) (bound : k < 268)
    (below : (k : Int) * 1024 < n.sizeZ) :
    ∃ bytes, n.blocks[k]? = some bytes ∧ n.data k = bytes ∧ bytes.length = 1024 := by
  have present := (h.domain k bound).mpr (h.covers k bound below)
  cases he : n.blocks[k]? with
  | none => simp [he] at present
  | some bytes => exact ⟨bytes, rfl, data_lookup _ _ _ he, h.blockLength _ _ he⟩

theorem local_beyond_size (h : Local inum n) (k : Nat) (bytes : List (BitVec 8))
    (lookup : n.blocks[k]? = some bytes) :
    k < 268 ∧ n.address k ≠ 0 ∧ bytes.length = 1024 := by
  have bound : k < 268 := by
    by_cases hb : k < 268
    · exact hb
    · have := h.top k (by omega)
      rw [lookup] at this
      contradiction
  exact ⟨bound, (h.domain k bound).mp (by simp [lookup]), h.blockLength _ _ lookup⟩

theorem blocksOfSeq_lookup (f : Nat → Option (List (BitVec 8)))
    (count start k : Nat) :
    (blocksOfSeq f start count)[k]? = if start ≤ k ∧ k < start + count then f k else none := by
  induction count generalizing start with
  | zero => simp only [blocksOfSeq, Std.ExtTreeMap.getElem?_empty, Nat.add_zero]
            rw [if_neg (by omega)]
  | succ count ih =>
    unfold blocksOfSeq
    cases hf : f start with
    | none =>
      rw [ih]
      by_cases hk : k = start
      · subst k; simp [hf]
      · have hc : (start + 1 ≤ k ∧ k < start + 1 + count) ↔
            (start ≤ k ∧ k < start + (count + 1)) := by omega
        simp only [hc]
    | some bytes =>
      rw [Std.ExtTreeMap.getElem?_insert]
      simp only [Std.compare_eq_eq_iff_eq]
      by_cases hk : start = k
      · subst k; simp [hf]
      · rw [if_neg hk, ih]
        have hc : (start + 1 ≤ k ∧ k < start + 1 + count) ↔
          (start ≤ k ∧ k < start + (count + 1)) := by omega
        simp only [hc]

theorem nodeOf_record (record : Dinode) (entries : List (BitVec 32)) (data : FileData) :
    (nodeOf record entries data).record = record := rfl

theorem nodeOf_entries (record : Dinode) (entries : List (BitVec 32)) (data : FileData) :
    (nodeOf record entries data).entries = entries := rfl

theorem nodeOf_address (record : Dinode) (entries : List (BitVec 32)) (data : FileData) (k : Nat) :
    (nodeOf record entries data).address k = (Node.mk record entries ∅).address k := rfl

theorem nodeOf_lookup (record : Dinode) (entries : List (BitVec 32)) (data : FileData) (k : Nat) :
    (nodeOf record entries data).blocks[k]? =
      if k < 268 ∧ (nodeOf record entries data).address k ≠ 0 then some (data k) else none := by
  change (blocksOfSeq _ 0 268)[k]? = _
  rw [blocksOfSeq_lookup]
  simp only [Nat.zero_le, true_and, Nat.zero_add, nodeOf_address]
  by_cases hb : k < 268 <;> by_cases hz : (Node.mk record entries ∅).address k = 0 <;>
    simp [hb, hz]

theorem bare_wf (h : n.Bare) : n.record.WellFormed := by
  simp [Dinode.WellFormed, h.1]

theorem bare_indirect (h : n.Bare) : n.indirect = 0 := by
  simp [Node.indirect, Dinode.addrZ, h.1]

theorem bare_address (h : n.Bare) (k : Nat) : n.address k = 0 := by
  unfold Node.address
  by_cases hb : k < 12
  · simp only [if_pos hb, Dinode.addrZ, h.1, List.getElem?_replicate,
      if_pos (show k < 13 by omega), Option.getD_some]; rfl
  · simp only [if_neg hb, h.2.1, List.getElem?_replicate]
    split <;> rfl

theorem bare_nrec (h : n.Bare) : n.nrec = 0 := by simp [Node.nrec, h.2.2.2.1, dirNrec]

theorem bare_orphan (h : n.Bare) : n.orphan = true := by simp [Node.orphan, h.2.2.2.2]

theorem bare_entries (h : n.Bare) : n.dirEntries = ∅ := by
  simp [Node.dirEntries, bare_nrec h, dirView, nameMap]

theorem bare_zero : zero.Bare := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bare_slot (h : n.Bare) (k : Nat) : n.slot k = 0 := by
  simp [Node.slot, bare_indirect h, bare_address h]

theorem bare_slot_injective (h : n.Bare) : n.SlotInjective := by
  intro k j hk hj hnz
  exact False.elim (hnz (bare_slot h k))

theorem bare_no_owns (h : n.Bare) (b : Int) : ¬ n.Owns b := by
  rintro (⟨k, hk, _⟩ | ⟨hnz, _⟩)
  · simp only [h.2.2.1, Std.ExtTreeMap.getElem?_empty, Option.isSome_none, Bool.false_eq_true] at hk
  · exact hnz (bare_indirect h)

theorem local_bare (h : n.Bare)
    (type : n.typeZ = 0 ∨ n.typeZ = 1 ∨ n.typeZ = 2 ∨ n.typeZ = 3) : Local inum n where
  record := bare_wf h
  entryLength := by rw [h.2.1, List.length_replicate]
  indirectZero := fun _ => h.2.1
  domain := by
    intro k hk
    simp only [h.2.2.1, Std.ExtTreeMap.getElem?_empty, Option.isSome_none,
      bare_address h k, ne_eq, not_true_eq_false, Bool.false_eq_true]
  top := by intro k hk; simp only [h.2.2.1, Std.ExtTreeMap.getElem?_empty]
  blockLength := by
    intro k bytes lookup
    simp only [h.2.2.1, Std.ExtTreeMap.getElem?_empty] at lookup
    contradiction
  type := type
  size := by rw [h.2.2.2.1]; decide
  covers := by
    intro k hk hlt
    rw [h.2.2.2.1] at hlt
    omega
  free := fun _ => h.2.2.2.2
  nlink := by
    have hn := h.2.2.2.2
    unfold Node.nlink at hn
    simp only [Dinode.nlinkZ, hn]
    decide
  dirSize := by intro _; rw [h.2.2.2.1]; exact ⟨0, rfl⟩
  dirUnique := by
    intro _ j k hj
    rw [bare_nrec h] at hj
    omega
  dirDot := by intro _ hn; exact False.elim (hn h.2.2.2.2)
  dirDotdot := by intro _ hn; exact False.elim (hn h.2.2.2.2)
  bareFree := fun _ => h

theorem local_zero (inum : Int) : Local inum zero := local_bare bare_zero (Or.inl rfl)

theorem dirLocal_not_dir (n : Node) (inum : Int) (nib : Nat) (h : n.typeZ ≠ 1) :
    DirLocal inum nib n := by
  refine ⟨?_, ?_, ?_⟩
  · intro ht; exact False.elim (h ht)
  · intro ht; exact False.elim (h (by change (n.record.type.toNat : Int) = 1; omega))
  · intro ht; exact False.elim (h ht)

theorem dirLocal_bare (n : Node) (inum : Int) (nib : Nat) (h : n.Bare) :
    DirLocal inum nib n := by
  refine ⟨?_, ?_, ?_⟩
  · intro ht k hk
    rw [bare_nrec h] at hk
    omega
  · intro ht hn
    have hz : n.record.nlink = 0 := BitVec.eq_of_toNat_eq h.2.2.2.2
    exact False.elim (hn hz)
  · intro ht hn k hk
    rw [bare_nrec h] at hk
    omega

theorem slot_data (n : Node) (k : Nat) (h : k < 268) : n.slot k = n.address k := by
  simp only [Node.slot, if_neg (show k ≠ 268 by omega)]

theorem slot_indirect (n : Node) : n.slot 268 = n.indirect := by unfold Node.slot; exact if_pos rfl

theorem slot_data_ne (h : n.SlotInjective) (k j : Nat) (hk : k < 268) (hj : j < 268)
    (nonzero : n.address k ≠ 0) (different : k ≠ j) : n.address k ≠ n.address j := by
  intro he
  apply different
  apply h k j (by omega) (by omega)
  · rwa [slot_data n k hk]
  · rwa [slot_data n k hk, slot_data n j hj]

theorem slot_indirect_ne (h : n.SlotInjective) (k : Nat) (hk : k < 268)
    (nonzero : n.address k ≠ 0) : n.address k ≠ n.indirect := by
  intro he
  have hk268 := h k 268 (by omega) (by omega)
    (by rwa [slot_data n k hk]) (by rwa [slot_data n k hk, slot_indirect])
  omega

/-- Node reconstruction recovers the original finite slot map under its
representation domain. No file size or content validity assumption is needed. -/
theorem nodeOf_rebuild (h : Repr n) : nodeOf n.record n.entries n.data = n := by
  have hm : (nodeOf n.record n.entries n.data).blocks = n.blocks := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    rw [nodeOf_lookup]
    change (if k < 268 ∧ n.address k ≠ 0 then some (n.data k) else none) = _
    by_cases hk : k < 268
    · cases he : n.blocks[k]? with
      | none =>
        have hz : n.address k = 0 := by
          by_cases hz : n.address k = 0
          · exact hz
          · have := (h.domain k hk).mpr hz
            simp [he] at this
        simp [hz]
      | some bytes =>
        have hz := (h.domain k hk).mp (by simp [he])
        rw [if_pos ⟨hk, hz⟩, data_lookup n k bytes he]
    · rw [if_neg (by omega), h.top k (by omega)]
  cases n with
  | mk record entries owned => exact congrArg (Node.mk record entries) hm

/-- A zero-link directory claim box owes no dot records. -/
theorem orphan_directory_local (inum : Int) :
    Local inum { zero with record := { zero.record with type := 1 } } :=
  local_bare ⟨rfl, rfl, rfl, rfl, rfl⟩ (Or.inr (Or.inl rfl))

theorem orphan_directory_entries :
    ({ zero with record := { zero.record with type := 1 } } : Node).dirEntries = ∅ :=
  bare_entries ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Nonzero addresses remain allocated when the record's size is zero. -/
theorem nodeOf_keeps_beyond_size (data : FileData) :
    (nodeOf { zero.record with addrs := 47 :: List.replicate 12 0 }
      zero.entries data).blocks[0]? = some (data 0) := by
  rw [nodeOf_lookup]
  rfl

/-- The range boundary itself is excluded even for a nonzero entry. -/
theorem nodeOf_excludes_top (record : Dinode) (entries : List (BitVec 32)) (data : FileData) :
    (nodeOf record entries data).blocks[268]? = none := by
  rw [nodeOf_lookup, if_neg (by omega)]

end Xv6.Fs.DurableNode

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "Xv6.Fs.DurableNode." ||
        name.toString.startsWith "_private.Xv6.Fs.DurableNode" then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} durable-node declarations; standard foundational axioms only."
