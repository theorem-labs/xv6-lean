import Xv6.Fs.BitmapSpec
import Xv6.Fs.InodeValidityProofs
import Init.Data.List.Pairwise
import Lean.Util.CollectAxioms

namespace Xv6.Fs

theorem collectNodup_mem (xs : List Int) (s : BlockSet)
    (h : collectNodup xs = some s) (x : Int) : x ∈ s ↔ x ∈ xs := by
  induction xs generalizing s with
  | nil =>
    simp only [collectNodup, Option.some.injEq] at h
    subst s
    simp
  | cons y ys ih =>
    simp only [collectNodup] at h
    cases hy : collectNodup ys with
    | none => simp [hy] at h
    | some t =>
      simp only [hy] at h
      split at h
      · contradiction
      · cases h
        simp only [Std.ExtTreeSet.mem_insert, Std.compare_eq_eq_iff_eq, ih t hy, List.mem_cons]
        simp only [eq_comm]

theorem collectNodup_nodup (xs : List Int) (s : BlockSet)
    (h : collectNodup xs = some s) : xs.Nodup := by
  induction xs generalizing s with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [collectNodup] at h
    cases ht : collectNodup xs with
    | none => simp [ht] at h
    | some t =>
      simp only [ht] at h
      split at h
      · contradiction
      · rename_i absent
        exact List.nodup_cons.mpr ⟨fun hx => absent ((collectNodup_mem xs t ht x).mpr hx), ih t ht⟩

theorem collectNodup_exists (xs : List Int) :
    (∃ s, collectNodup xs = some s) ↔ xs.Nodup := by
  constructor
  · rintro ⟨s, hs⟩; exact collectNodup_nodup xs s hs
  · intro h
    induction xs with
    | nil => exact ⟨∅, rfl⟩
    | cons x xs ih =>
      obtain ⟨absent, tail⟩ := List.nodup_cons.mp h
      obtain ⟨s, hs⟩ := ih tail
      refine ⟨s.insert x, ?_⟩
      have hn : x ∉ s := fun hx => absent ((collectNodup_mem xs s hs x).mp hx)
      simp [collectNodup, hs, hn]

theorem collectNodup_none (xs : List Int) :
    collectNodup xs = none ↔ ¬ xs.Nodup := by
  rw [← collectNodup_exists]
  cases collectNodup xs <;> simp

theorem usedSet_nodup image sb used (h : usedSet image sb = some used) :
    (usedBlocks image sb).Nodup := collectNodup_nodup _ _ h

theorem usedSet_mem image sb used (h : usedSet image sb = some used) b :
    b ∈ used ↔ b ∈ usedBlocks image sb := collectNodup_mem _ _ h b

theorem usedSet_none image sb : usedSet image sb = none ↔ ¬ (usedBlocks image sb).Nodup :=
  collectNodup_none _

theorem inodeBlocks_eq_inputs image dn :
    inodeBlocks image dn = inodeBlocksInput dn (indirectEntries image dn) := rfl

theorem usedBlocks_eq_live image sb :
    usedBlocks image sb = (liveInodes image sb).flatMap
      (fun i => inodeBlocks image (dinode image sb i)) := by
  have helper (xs : List Nat) :
      (xs.map (fun (i : Nat) => if (dinode image sb (i : Int)).typeZ == 0 then []
        else inodeBlocks image (dinode image sb (i : Int)))).flatten =
      ((xs.map Int.ofNat).filter (fun i => !((dinode image sb i).typeZ == 0))).flatMap
        (fun i => inodeBlocks image (dinode image sb i)) := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      by_cases free : (dinode image sb (i : Int)).typeZ = 0
      · simpa [free] using ih
      · simpa [free] using congrArg (inodeBlocks image (dinode image sb (i : Int)) ++ ·) ih
  exact helper _

theorem inodeBlocks_mem_chunks (image : Blocks) (sb : Superblock) (i : Int)
    (bound : 0 ≤ i ∧ i < sb.ninodes) (live : (dinode image sb i).typeZ ≠ 0) :
    inodeBlocks image (dinode image sb i) ∈
      (List.range sb.ninodes.toNat).map (fun (j : Nat) =>
        if (dinode image sb (j : Int)).typeZ == 0 then []
        else inodeBlocks image (dinode image sb (j : Int))) := by
  apply List.mem_map.mpr
  refine ⟨i.toNat, List.mem_range.mpr (by omega), ?_⟩
  simp [Int.toNat_of_nonneg bound.1, live]

theorem usedBlocks_inode (image : Blocks) (sb : Superblock) (i b : Int)
    (bound : 0 ≤ i ∧ i < sb.ninodes) (live : (dinode image sb i).typeZ ≠ 0)
    (member : b ∈ inodeBlocks image (dinode image sb i)) : b ∈ usedBlocks image sb := by
  exact List.mem_flatten.mpr ⟨_, inodeBlocks_mem_chunks image sb i bound live, member⟩

theorem nodup_flatten_member {α : Type} (chunks : List (List α)) (xs : List α)
    (nd : chunks.flatten.Nodup) (member : xs ∈ chunks) : xs.Nodup := by
  induction chunks with
  | nil => simp at member
  | cons ys rest ih =>
    simp only [List.mem_cons] at member
    obtain ⟨left, right, _⟩ := List.nodup_append.mp nd
    rcases member with rfl | member
    · exact left
    · exact ih right member

theorem usedBlocks_nodup_inode (image : Blocks) (sb : Superblock) (i : Int)
    (nd : (usedBlocks image sb).Nodup) (bound : 0 ≤ i ∧ i < sb.ninodes)
    (live : (dinode image sb i).typeZ ≠ 0) :
    (inodeBlocks image (dinode image sb i)).Nodup :=
  nodup_flatten_member _ _ nd (inodeBlocks_mem_chunks image sb i bound live)

theorem inodeBlockSet_mem image sb i b :
    b ∈ inodeBlockSet image sb i ↔ b ∈ inodeBlocks image (dinode image sb i) := by
  simp [inodeBlockSet, Std.ExtTreeSet.mem_ofList]

theorem bitmapValid_iff (image : Blocks) (sb : Superblock) (used : BlockSet) :
    bitmapValid image sb used = true ↔ BitmapOK image sb used := by
  unfold bitmapValid BitmapOK
  rw [List.all_eq_true]
  constructor
  · intro h b bound
    have hb := h b.toNat (List.mem_range.mpr (by omega))
    have cast : (b.toNat : Int) = b := Int.toNat_of_nonneg bound.1
    have eq : bitmapBit (image sb.bmapstart) b =
        (decide (b < dataStart sb) || decide (b ∈ used)) := by
      simpa only [cast, beq_iff_eq] using hb
    rw [eq]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
  · intro h i hi
    have hi := List.mem_range.mp hi
    have hb := h (i : Int) ⟨by omega, by omega⟩
    apply beq_iff_eq.mpr
    apply Bool.eq_iff_iff.mpr
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using hb

theorem bitmapValid_spec image sb used (valid : bitmapValid image sb used = true)
    b (bound : 0 ≤ b ∧ b < sb.size) :
    bitmapBit (image sb.bmapstart) b = true ↔ b < dataStart sb ∨ b ∈ used :=
  (bitmapValid_iff image sb used).mp valid b bound

theorem bitmapValid_free image sb used (valid : bitmapValid image sb used = true)
    b (bound : 0 ≤ b ∧ b < sb.size) (clear : bitmapBit (image sb.bmapstart) b = false) :
    dataStart sb ≤ b ∧ b ∉ used := by
  have iff := bitmapValid_spec image sb used valid b bound
  have absent : ¬ (b < dataStart sb ∨ b ∈ used) := by
    intro h
    have := iff.mpr h
    simp [clear] at this
  exact ⟨by omega, fun hu => absent (Or.inr hu)⟩

theorem bitmapValid_metadata image sb used (valid : bitmapValid image sb used = true)
    b (bound : 0 ≤ b ∧ b < sb.size) (metadata : b < dataStart sb) :
    bitmapBit (image sb.bmapstart) b = true :=
  (bitmapValid_spec image sb used valid b bound).mpr (Or.inl metadata)

theorem bitmapValid_used image sb used (valid : bitmapValid image sb used = true)
    b (bound : 0 ≤ b ∧ b < sb.size) (member : b ∈ used) :
    bitmapBit (image sb.bmapstart) b = true :=
  (bitmapValid_spec image sb used valid b bound).mpr (Or.inr member)

theorem bitmapSet_mem n bytes b : b ∈ bitmapSet n bytes ↔
    (0 ≤ b ∧ b < 8 * (n : Int)) ∧ bitmapBit bytes b = true := by
  simp only [bitmapSet, Std.ExtTreeSet.mem_ofList, List.contains_iff_mem,
    List.mem_filter, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, bit⟩
    refine ⟨?_, bit⟩
    change 0 ≤ (i : Int) ∧ (i : Int) < 8 * (n : Int)
    omega
  · rintro ⟨bound, bit⟩
    exact ⟨⟨b.toNat, by omega, Int.toNat_of_nonneg bound.1⟩, bit⟩

theorem bitmapSet_free image sb used (n : Nat) (valid : bitmapValid image sb used = true)
    (oneBitmap : sb.size ≤ 8 * (n : Int)) b (bound : 0 ≤ b ∧ b < sb.size)
    (free : b ∉ bitmapSet n (image sb.bmapstart)) : dataStart sb ≤ b ∧ b ∉ used := by
  apply bitmapValid_free image sb used valid b bound
  cases bit : bitmapBit (image sb.bmapstart) b with
  | false => rfl
  | true => exact False.elim (free ((bitmapSet_mem n _ b).mpr ⟨⟨bound.1, by omega⟩, bit⟩))

theorem blocksBitmapValid_iff image sb :
    blocksBitmapValid image sb = true ↔ BlocksBitmapOK image sb := by
  unfold blocksBitmapValid BlocksBitmapOK
  cases h : usedSet image sb with
  | none => simp
  | some used =>
    simp only [Option.some.injEq, exists_eq_left']
    exact ⟨fun valid => ⟨usedSet_nodup image sb used h, (bitmapValid_iff ..).mp valid⟩,
      fun valid => (bitmapValid_iff ..).mpr valid.2⟩

theorem inodeBlocks_range image sb dn (ok : InodeOK image sb dn) b
    (member : b ∈ inodeBlocks image dn) : dataStart sb ≤ b ∧ b < sb.size := by
  have nb := nblk_max dn.sizeZ (by unfold Dinode.sizeZ; omega) ok.size
  simp only [inodeBlocks, List.mem_append, List.mem_map, List.mem_range] at member
  rcases member with ind | direct | entry
  · split at ind
    · rename_i indirect
      simp only [List.mem_singleton] at ind
      subst b
      exact ok.ind indirect
    · simp at ind
  · obtain ⟨i, hi, rfl⟩ := direct
    exact ok.direct i (by omega) (by omega)
  · obtain ⟨i, hi, rfl⟩ := entry
    exact ok.ent i (by omega) (by omega)

theorem usedBlocks_range image sb (valid : inodesValid image sb = true) b
    (member : b ∈ usedBlocks image sb) : dataStart sb ≤ b ∧ b < sb.size := by
  obtain ⟨chunk, hc, hb⟩ := List.mem_flatten.mp member
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  have bound := List.mem_range.mp hi
  dsimp only at hb
  split at hb
  · simp at hb
  · rename_i live
    apply inodeBlocks_range image sb _ ?_ b hb
    exact inodesValid_spec image sb (i : Int) valid ⟨by omega, by omega⟩ (by simpa using live)

theorem bitmapBit_testBit bytes b : bitmapBit bytes b =
    (bytes[(b / 8).toNat]?.getD 0).toNat.testBit (b % 8).toNat := rfl

theorem bitmapBit_empty b : bitmapBit [] b = false := by simp [bitmapBit]

theorem bitmapBit_index_bound (b : Int) : 0 ≤ b % 8 ∧ b % 8 < 8 := by omega

/-- Source Z.to_nat sends the negative quotient to zero, preserving byte-zero reads. -/
theorem bitmapBit_negative_regression : bitmapBit [128#8] (-1) = true := by decide

theorem duplicate_rejected : collectNodup [47, 48, 47] = none := by decide

theorem signed_distinct_collected : ∃ s, collectNodup [-1, 0, 1] = some s := by
  apply (collectNodup_exists _).mpr
  decide

/-- Bit zero is metadata when size/dataStart are positive. -/
theorem bitmapValid_zero image sb used (valid : bitmapValid image sb used = true)
    (size : 0 < sb.size) (metadata : 0 < dataStart sb) :
    bitmapBit (image sb.bmapstart) 0 = true :=
  bitmapValid_metadata image sb used valid 0 ⟨by omega, size⟩ metadata

/-- Only the size-one prefix is checked, so bit seven is intentionally unconstrained. -/
theorem bitmap_padding_unconstrained :
    bitmapValid (fun _ => [129#8]) ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ ∅ = true := by decide

theorem bitmap_zero_rejected :
    bitmapValid (fun _ => [0#8]) ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ ∅ = false := by decide

theorem bitmap_negative_size_vacuous image sb used (size : sb.size ≤ 0) :
    bitmapValid image sb used = true := by
  have zero : sb.size.toNat = 0 := by omega
  simp [bitmapValid, zero]

end Xv6.Fs

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs.") then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} filesystem/bitmap theorem cones; standard foundational axioms only."
