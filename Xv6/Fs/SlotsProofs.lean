import Xv6.Fs.SlotsDefs
import Xv6.Fs.DurableInodeProofs

namespace Xv6.Fs

theorem slot_max image dn : slot image dn 268 = dn.addrZ 12 := by simp [slot]

theorem slot_lt image dn i (bound : i < 268) : slot image dn i = blockAddress image dn i := by
  simp only [slot, show i ≠ 268 by omega, ↓reduceIte]

theorem slot_direct image dn i (bound : i < 12) : slot image dn i = dn.addrZ i := by
  rw [slot_lt image dn i (by omega)]
  simp only [blockAddress, bound, ↓reduceIte, Dinode.addrZ]

theorem slot_entry image dn i (lower : 12 ≤ i) (upper : i < 268) :
    slot image dn i = (indirectEntries image dn)[i - 12]?.getD 0 := by
  rw [slot_lt image dn i upper]
  simp only [blockAddress, show ¬ i < 12 by omega, ↓reduceIte]

theorem slot_det image image' dn dn' i (addrs : dn'.addrs = dn.addrs)
    (entries : indirectEntries image' dn' = indirectEntries image dn) :
    slot image' dn' i = slot image dn i := by
  simp only [slot, blockAddress, Dinode.addrZ, addrs, entries]

theorem runIndex_injective i j (hi : i ≤ 268) (hj : j ≤ 268)
    (eq : runIndex i = runIndex j) : i = j := by
  simp only [runIndex] at eq
  split at eq <;> split at eq <;> omega

theorem runIndex_bound i (bound : i ≤ 268) : runIndex i < 269 := by
  unfold runIndex
  split <;> omega

theorem runIndex_surjective k (bound : k < 269) : ∃ i, i ≤ 268 ∧ runIndex i = k := by
  cases k with
  | zero => exact ⟨268, by omega, by simp [runIndex]⟩
  | succ k => exact ⟨k, by omega, by simp [runIndex, show k ≠ 268 by omega]⟩

theorem slotList_length image dn : (slotList image dn).length = 269 := by
  simp only [slotList, List.length_cons, List.length_append, List.length_map,
    List.length_range, indirectEntries_length]

theorem slotList_lookup image dn i (bound : i ≤ 268) :
    (slotList image dn)[runIndex i]? = some (slot image dn i) := by
  by_cases last : i = 268
  · subst i
    simp only [runIndex, ↓reduceIte, slotList, List.getElem?_cons_zero, slot_max]
  · simp only [runIndex, last, ↓reduceIte, slotList, List.getElem?_cons_succ]
    by_cases direct : i < 12
    · rw [List.getElem?_append_left (by simpa using direct), List.getElem?_map,
        List.getElem?_range direct]
      rw [slot_direct image dn i direct]
      rfl
    · rw [List.getElem?_append_right (by simp only [List.length_map, List.length_range]; omega)]
      simp only [List.length_map, List.length_range]
      rw [slot_entry image dn i (by omega) (by omega)]
      have inside : i - 12 < (indirectEntries image dn).length := by rw [indirectEntries_length]; omega
      rw [List.getElem?_eq_getElem inside]
      rfl

theorem slotList_member image dn b : b ∈ slotList image dn ↔
    ∃ i, i ≤ 268 ∧ slot image dn i = b := by
  constructor
  · intro member
    obtain ⟨k, lookup⟩ := List.mem_iff_getElem?.mp member
    have bound : k < 269 := by
      rw [← slotList_length image dn]
      exact (List.getElem?_eq_some_iff.mp lookup).1
    obtain ⟨i, hi, eq⟩ := runIndex_surjective k bound
    rw [← eq, slotList_lookup image dn i hi] at lookup
    exact ⟨i, hi, Option.some.inj lookup⟩
  · rintro ⟨i, hi, rfl⟩
    exact List.mem_iff_getElem?.mpr ⟨runIndex i, slotList_lookup image dn i hi⟩

theorem inodeEntries_member image dn b : b ∈ inodeEntries image dn ↔
    ∃ i, i ≤ 268 ∧ slot image dn i = b ∧ b ≠ 0 := by
  simp only [inodeEntries, List.mem_filter, Bool.not_eq_true', beq_eq_false_iff_ne,
    slotList_member]
  constructor
  · rintro ⟨⟨i, hi, eq⟩, nz⟩
    exact ⟨i, hi, eq, nz⟩
  · rintro ⟨i, hi, eq, nz⟩
    exact ⟨⟨i, hi, eq⟩, nz⟩

theorem inodeEntries_slot image dn i (bound : i ≤ 268) (nz : slot image dn i ≠ 0) :
    slot image dn i ∈ inodeEntries image dn :=
  (inodeEntries_member image dn _).mpr ⟨i, bound, rfl, nz⟩

theorem inodeEntries_range image sb dn (ok : InodeDurableOK image sb dn) b
    (member : b ∈ inodeEntries image dn) : dataStart sb ≤ b ∧ b < sb.size := by
  obtain ⟨i, hi, eq, nz⟩ := (inodeEntries_member image dn b).mp member
  rw [← eq] at nz ⊢
  by_cases last : i = 268
  · subst i
    rw [slot_max] at nz ⊢
    exact ok.ind_ok nz
  · by_cases direct : i < 12
    · rw [slot_direct image dn i direct] at nz ⊢
      exact ok.direct_ok i direct nz
    · rw [slot_entry image dn i (by omega) (by omega)] at nz ⊢
      exact ok.ent_ok (i - 12) (by omega) nz

theorem inodeEntries_det image image' dn dn' (addrs : dn'.addrs = dn.addrs)
    (entries : indirectEntries image' dn' = indirectEntries image dn) :
    inodeEntries image' dn' = inodeEntries image dn := by
  have addr : dn'.addrZ = dn.addrZ := by
    funext k
    simp only [Dinode.addrZ, addrs]
  simp only [inodeEntries, slotList, addr, entries]

theorem inodeEntries_chunks image dn : inodeEntries image dn =
    (if dn.addrZ 12 == 0 then [] else [dn.addrZ 12]) ++
    ((List.range 12).map dn.addrZ).filter (fun a => !(a == 0)) ++
    (indirectEntries image dn).filter (fun a => !(a == 0)) := by
  simp only [inodeEntries, slotList, List.filter_cons, List.filter_append]
  split <;> simp_all only [Bool.not_eq_true',
    Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]

/-- A kept value in a duplicate-free filter has one position in the original list. -/
theorem nodup_filter_lookup_injective {α : Type} (p : α → Bool) (xs : List α)
    (nd : (xs.filter p).Nodup) (i j : Nat) (x : α)
    (left : xs[i]? = some x) (right : xs[j]? = some x) (keep : p x = true) : i = j := by
  induction xs generalizing i j with
  | nil => simp at left
  | cons a xs ih =>
    have mem (k : Nat) (h : xs[k]? = some x) : x ∈ xs.filter p :=
      List.mem_filter.mpr ⟨List.mem_iff_getElem?.mpr ⟨k, h⟩, keep⟩
    have tail : (xs.filter p).Nodup := by
      by_cases pa : p a = true
      · have both := List.nodup_cons.mp (show (a :: xs.filter p).Nodup by
          simpa only [List.filter_cons, pa, ↓reduceIte] using nd)
        exact both.2
      · simpa only [List.filter_cons, pa, Bool.false_eq_true, ↓reduceIte] using nd
    cases i with
    | zero =>
      have ax : a = x := Option.some.inj left
      subst a
      cases j with
      | zero => rfl
      | succ j =>
        have bad := (List.nodup_cons.mp (by simpa only [List.filter_cons, keep, ↓reduceIte] using nd)).1
        exact False.elim (bad (mem j right))
    | succ i =>
      cases j with
      | zero =>
        have ax : a = x := Option.some.inj right
        subst a
        have bad := (List.nodup_cons.mp (by simpa only [List.filter_cons, keep, ↓reduceIte] using nd)).1
        exact False.elim (bad (mem i left))
      | succ j => exact congrArg Nat.succ (ih tail i j left right)

theorem slotInjective_of_entries image dn (nd : (inodeEntries image dn).Nodup) : SlotInjective image dn := by
  intro i j hi hj nz eq
  apply runIndex_injective i j hi hj
  apply nodup_filter_lookup_injective (fun a : Int => !(a == 0)) (slotList image dn) nd
    (runIndex i) (runIndex j) (slot image dn i)
  · exact slotList_lookup image dn i hi
  · rw [eq]
    exact slotList_lookup image dn j hj
  · simp only [beq_eq_false_iff_ne.mpr nz, Bool.not_false]

theorem slotList_update image image' dn dn' j a (bound : j ≤ 268)
    (changed : slot image' dn' j = a)
    (preserved : ∀ k, k ≤ 268 → k ≠ j → slot image' dn' k = slot image dn k) :
    slotList image' dn' = (slotList image dn).set (runIndex j) a := by
  apply List.ext_getElem?
  intro k
  by_cases inside : k < 269
  · obtain ⟨i, hi, rfl⟩ := runIndex_surjective k inside
    rw [slotList_lookup image' dn' i hi]
    by_cases equal : i = j
    · subst i
      rw [List.getElem?_set_self (by rw [slotList_length]; exact runIndex_bound j bound), changed]
    · rw [List.getElem?_set_ne (by intro eq; exact equal (runIndex_injective i j hi bound eq.symm)),
        slotList_lookup image dn i hi, preserved i hi equal]
  · rw [List.getElem?_eq_none_iff.mpr (by rw [slotList_length]; omega),
      List.getElem?_eq_none_iff.mpr (by rw [List.length_set, slotList_length]; omega)]

/-- Filling a zero entry adds one occurrence, irrespective of its position. -/
theorem filter_nonzero_update (xs : List Int) (j : Nat) (a : Int)
    (zero : xs[j]? = some 0) (nonzero : a ≠ 0) :
    ((xs.set j a).filter (fun x => !(x == 0))).Perm
      (xs.filter (fun x => !(x == 0)) ++ [a]) := by
  induction xs generalizing j with
  | nil => simp at zero
  | cons x xs ih =>
    cases j with
    | zero =>
      have eq : x = 0 := Option.some.inj zero
      subst x
      simp only [List.set_cons_zero, List.filter_cons, beq_eq_false_iff_ne.mpr nonzero,
        Bool.not_false, BEq.rfl, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact (List.perm_append_singleton _ _).symm
    | succ j =>
      have tail := ih j zero
      simp only [List.set_cons_succ, List.filter_cons]
      split
      · exact List.Perm.cons x tail
      · exact tail

theorem inodeEntries_update image image' dn dn' j a (bound : j ≤ 268) (nonzero : a ≠ 0)
    (zero : slot image dn j = 0) (changed : slot image' dn' j = a)
    (preserved : ∀ k, k ≤ 268 → k ≠ j → slot image' dn' k = slot image dn k) :
    (inodeEntries image' dn').Perm (inodeEntries image dn ++ [a]) := by
  unfold inodeEntries
  rw [slotList_update image image' dn dn' j a bound changed preserved]
  apply filter_nonzero_update _ _ _ _ nonzero
  rw [slotList_lookup image dn j bound, zero]

theorem runIndex_boundary_regression : runIndex 268 = 0 ∧ runIndex 267 = 268 := by decide

private def aliasedSlotsRecord : Dinode := ⟨2, 0, 0, 1, 0, [47] ++ List.replicate 11 0 ++ [47]⟩

theorem indirect_root_alias_rejected : ¬ SlotInjective (fun _ => []) aliasedSlotsRecord := by
  intro injective
  have impossible := injective 0 268 (by decide) (by decide) (by decide) (by decide)
  omega

theorem slot_outside_direct_defaults : slot (fun _ => []) (default : Dinode) 0 = 0 := by decide

end Xv6.Fs

open Lean Elab Command in
run_cmd do
  for (name, info) in (← getEnv).constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs.") then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
