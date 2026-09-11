import Xv6.Fs.DurableBlocksDefs
import Xv6.Fs.SlotsProofs
import Xv6.Fs.BitmapProofs

namespace Xv6.Fs

theorem dataStart_positive sb (ok : SuperblockOK sb) : 0 < dataStart sb := by
  have h := superblock_metadata sb ok
  omega

/-- Filtering a run nonzero exactly below m preserves that prefix's order. -/
theorem filter_nonzero_prefix (f : Nat → Int) (n m : Nat) (bound : m ≤ n)
    (below : ∀ k < m, f k ≠ 0) (above : ∀ k, m ≤ k → k < n → f k = 0) :
    ((List.range n).map f).filter (fun x => !(x == 0)) = (List.range m).map f := by
  have split : List.range n = List.range m ++ (List.range (n - m)).map (m + ·) := by
    rw [← List.range_add]
    congr 1
    omega
  rw [split, List.map_append, List.filter_append]
  have low : ((List.range m).map f).filter (fun x => !(x == 0)) = (List.range m).map f := by
    apply List.filter_eq_self.mpr
    rintro _ member
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp member
    simp only [beq_eq_false_iff_ne.mpr (below k (List.mem_range.mp hk)), Bool.not_false]
  have high : (((List.range (n - m)).map (m + ·)).map f).filter (fun x => !(x == 0)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    rintro _ member
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp member
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
    have boundj := List.mem_range.mp hj
    simp only [above (m + j) (by omega) (by omega), BEq.rfl, Bool.not_true, Bool.false_eq_true, not_false_eq_true]
  rw [low, high, List.append_nil]

theorem list_total_range (xs : List Int) : (List.range xs.length).map (fun j => xs[j]?.getD 0) = xs := by
  apply List.ext_getElem?
  intro k
  by_cases bound : k < xs.length
  · rw [List.getElem?_map, List.getElem?_range bound, List.getElem?_eq_getElem bound]
    simp only [Option.map_some, List.getElem?_eq_getElem bound, Option.getD_some]
  · rw [List.getElem?_eq_none_iff.mpr (by simp only [List.length_map, List.length_range]; omega),
      List.getElem?_eq_none_iff.mpr (by omega)]

theorem inodeEntries_eq_blocks image sb dn (geometry : SuperblockOK sb) (ok : InodeOK image sb dn) :
    inodeEntries image dn = inodeBlocks image dn := by
  have positive := dataStart_positive sb geometry
  have lower : 0 ≤ nblk dn.sizeZ := by unfold nblk Dinode.sizeZ; omega
  have upper : nblk dn.sizeZ ≤ 268 := by have := ok.size; unfold nblk; omega
  have direct : ((List.range 12).map dn.addrZ).filter (fun x => !(x == 0)) =
      (List.range (min (nblk dn.sizeZ) 12).toNat).map dn.addrZ := by
    apply filter_nonzero_prefix
    · omega
    · intro k hk
      have h := ok.direct k (by omega) (by omega)
      omega
    · intro k low high
      exact ok.direct_zero k high (by omega)
  have entries : (indirectEntries image dn).filter (fun x => !(x == 0)) =
      (List.range (nblk dn.sizeZ - 12).toNat).map (fun j => (indirectEntries image dn)[j]?.getD 0) := by
    have total : (List.range 256).map (fun j => (indirectEntries image dn)[j]?.getD 0) =
        indirectEntries image dn := by
      simpa only [indirectEntries_length] using list_total_range (indirectEntries image dn)
    calc
      _ = ((List.range 256).map (fun j => (indirectEntries image dn)[j]?.getD 0)).filter
          (fun x => !(x == 0)) := congrArg (List.filter (fun x => !(x == 0))) total.symm
      _ = _ := by
        apply filter_nonzero_prefix
        · omega
        · intro j hj
          have h := ok.ent j (by omega) (by omega)
          omega
        · intro j low high
          exact ok.ent_zero j high (by omega)
  rw [inodeEntries_chunks, direct, entries]
  unfold inodeBlocks
  by_cases large : 12 < nblk dn.sizeZ
  · have nz : dn.addrZ 12 ≠ 0 := by have := ok.ind large; omega
    simp only [beq_eq_false_iff_ne.mpr nz, Bool.false_eq_true, large, ↓reduceIte, List.append_assoc]
  · simp only [ok.ind_zero (by omega), BEq.rfl, ↓reduceIte, large, List.append_assoc]

theorem entryBlocks_eq_used image sb (geometry : SuperblockOK sb) (valid : inodesValid image sb = true) :
    entryBlocks image sb = usedBlocks image sb := by
  unfold entryBlocks usedBlocks
  congr 1
  apply List.map_congr_left
  intro i hi
  by_cases free : (dinode image sb (i : Int)).typeZ = 0
  · simp only [free, BEq.rfl, ↓reduceIte]
  · simp only [beq_eq_false_iff_ne.mpr free, Bool.false_eq_true, ↓reduceIte]
    apply inodeEntries_eq_blocks image sb _ geometry
    exact inodesValid_spec image sb _ valid ⟨by omega, by have := List.mem_range.mp hi; omega⟩ free

theorem entrySet_eq_used image sb (geometry : SuperblockOK sb) (valid : inodesValid image sb = true) :
    entrySet image sb = usedSet image sb := by
  unfold entrySet usedSet
  rw [entryBlocks_eq_used image sb geometry valid]

theorem entrySet_nodup image sb used (eq : entrySet image sb = some used) : (entryBlocks image sb).Nodup :=
  collectNodup_nodup _ _ eq

theorem entrySet_member image sb used (eq : entrySet image sb = some used) b :
    b ∈ used ↔ b ∈ entryBlocks image sb := collectNodup_mem _ _ eq b

theorem inodeEntries_mem_chunks image sb i (bound : 0 ≤ i ∧ i < sb.ninodes)
    (live : (dinode image sb i).typeZ ≠ 0) :
    inodeEntries image (dinode image sb i) ∈
      (List.range sb.ninodes.toNat).map (fun (j : Nat) =>
        if (dinode image sb (j : Int)).typeZ == 0 then []
        else inodeEntries image (dinode image sb (j : Int))) := by
  apply List.mem_map.mpr
  refine ⟨i.toNat, List.mem_range.mpr (by omega), ?_⟩
  simp only [Int.toNat_of_nonneg bound.1, beq_eq_false_iff_ne.mpr live,
    Bool.false_eq_true, ↓reduceIte]

theorem entryBlocks_inode image sb i b (bound : 0 ≤ i ∧ i < sb.ninodes)
    (live : (dinode image sb i).typeZ ≠ 0) (member : b ∈ inodeEntries image (dinode image sb i)) :
    b ∈ entryBlocks image sb :=
  List.mem_flatten.mpr ⟨_, inodeEntries_mem_chunks image sb i bound live, member⟩

theorem entryBlocks_nodup_inode image sb i (nd : (entryBlocks image sb).Nodup)
    (bound : 0 ≤ i ∧ i < sb.ninodes) (live : (dinode image sb i).typeZ ≠ 0) :
    (inodeEntries image (dinode image sb i)).Nodup :=
  nodup_flatten_member _ _ nd (inodeEntries_mem_chunks image sb i bound live)

theorem nodup_flatten_cross {α : Type} (chunks : List (List α)) (i j : Nat) (xs ys : List α)
    (nd : chunks.flatten.Nodup) (left : chunks[i]? = some xs) (right : chunks[j]? = some ys)
    (different : i ≠ j) (b : α) (hx : b ∈ xs) (hy : b ∈ ys) : False := by
  induction chunks generalizing i j with
  | nil => simp at left
  | cons zs rest ih =>
    obtain ⟨_, tail, apart⟩ := List.nodup_append.mp nd
    cases i with
    | zero =>
      have eq : zs = xs := Option.some.inj left
      subst zs
      cases j with
      | zero => exact different rfl
      | succ j =>
        exact apart b hx b (List.mem_flatten.mpr ⟨ys, List.mem_iff_getElem?.mpr ⟨j, right⟩, hy⟩) rfl
    | succ i =>
      cases j with
      | zero =>
        have eq : zs = ys := Option.some.inj right
        subst zs
        exact apart b hy b (List.mem_flatten.mpr ⟨xs, List.mem_iff_getElem?.mpr ⟨i, left⟩, hx⟩) rfl
      | succ j => exact ih i j tail left right (by omega)

theorem inodeEntrySet_member image sb i b : b ∈ inodeEntrySet image sb i ↔
    b ∈ inodeEntries image (dinode image sb i) := by
  simp only [inodeEntrySet, Std.ExtTreeSet.mem_ofList, List.contains_iff_mem]

/-- Extensional set disjointness, with the exact bounded live-inode premises. -/
theorem inodeEntrySet_disjoint image sb i j (nd : (entryBlocks image sb).Nodup)
    (hi : 0 ≤ i ∧ i < sb.ninodes) (hj : 0 ≤ j ∧ j < sb.ninodes) (different : i ≠ j)
    (li : (dinode image sb i).typeZ ≠ 0) (lj : (dinode image sb j).typeZ ≠ 0) :
    ∀ b, b ∈ inodeEntrySet image sb i → b ∈ inodeEntrySet image sb j → False := by
  intro b bi bj
  apply nodup_flatten_cross _ i.toNat j.toNat _ _ nd _ _ (by omega) b
    ((inodeEntrySet_member image sb i b).mp bi) ((inodeEntrySet_member image sb j b).mp bj)
  · rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Int.toNat_of_nonneg hi.1, beq_eq_false_iff_ne.mpr li,
      Bool.false_eq_true, ↓reduceIte]
  · rw [List.getElem?_map, List.getElem?_range (by omega)]
    simp only [Option.map_some, Int.toNat_of_nonneg hj.1, beq_eq_false_iff_ne.mpr lj,
      Bool.false_eq_true, ↓reduceIte]

theorem usedBlocks_slot_injective image sb i (geometry : SuperblockOK sb)
    (valid : inodesValid image sb = true) (nd : (usedBlocks image sb).Nodup)
    (bound : 0 ≤ i ∧ i < sb.ninodes) (live : (dinode image sb i).typeZ ≠ 0) :
    SlotInjective image (dinode image sb i) := by
  apply slotInjective_of_entries
  rw [inodeEntries_eq_blocks image sb _ geometry (inodesValid_spec image sb i valid bound live)]
  exact usedBlocks_nodup_inode image sb i nd bound live

theorem InodeDurableOK.block image sb dn (ok : InodeDurableOK image sb dn)
    (k : Nat) (bound : k < 268) (below : (k : Int) < nblk dn.sizeZ) :
    dataStart sb ≤ blockAddress image dn k ∧ blockAddress image dn k < sb.size := by
  unfold blockAddress
  split
  · exact ok.direct k ‹_› below
  · exact ok.ent (k - 12) (by omega) (by omega)

end Xv6.Fs

open Lean Elab Command in
run_cmd do
  for (name, info) in (← getEnv).constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs.") then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
