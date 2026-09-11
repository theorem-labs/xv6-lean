import MachCSL.Logic.FsDurAllocSeparationProofs

namespace MachCSL.Logic.FsDurAlloc
open Iris Iris.Std Xv6.Fs DurableState DurableNode

theorem inodes_mem state i : i ∈ inodes state ↔ state.inodes[i]?.isSome := by
  simp only [inodes, _root_.Std.ExtTreeMap.mem_keys, _root_.Std.ExtTreeMap.mem_iff_isSome_getElem?]

theorem dataSlots_mem state slot : slot ∈ dataSlots state ↔
    ∃ i k, state.inodes[i]?.isSome ∧ (nodeAt state i).blocks[k]?.isSome ∧ slot = Slot.data i k := by
  simp only [dataSlots, List.mem_flatMap, List.mem_map, inodes_mem,
    _root_.Std.ExtTreeMap.mem_keys, _root_.Std.ExtTreeMap.mem_iff_isSome_getElem?]
  constructor
  · rintro ⟨i, hi, k, hk, same⟩
    exact ⟨i, k, hi, hk, same.symm⟩
  · rintro ⟨i, k, hi, hk, same⟩
    exact ⟨i, hi, k, hk, same.symm⟩

theorem pools_mem state slot : slot ∈ pools state ↔
    ∃ b : Int, 0 ≤ b ∧ b < state.superblock.size ∧ slot = Slot.pool b := by
  simp only [pools, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, by omega, by omega, rfl⟩
  · rintro ⟨b, nonneg, bound, rfl⟩
    exact ⟨b.toNat, by omega, congrArg Slot.pool (Int.toNat_of_nonneg nonneg)⟩

theorem family_mem state slot : slot ∈ family state ↔ Valid state slot := by
  cases slot <;>
    simp [family, records, indirects, List.mem_map, inodes_mem, dataSlots_mem, pools_mem, Valid]

private theorem nodup_map_injective {A B : Type} (f : A → B) (list : List A)
    (injective : ∀ a b, f a = f b → a = b) (nodup : list.Nodup) : (list.map f).Nodup :=
  nodup.map f (fun a b different same => different (injective a b same))

theorem family_nodup state : (family state).Nodup := by
  have inodeKeys : (inodes state).Nodup := _root_.Std.ExtTreeMap.nodup_keys
  have recs : (records state).Nodup := nodup_map_injective Slot.record _ (fun _ _ eq => Slot.record.inj eq) inodeKeys
  have inds : (indirects state).Nodup := nodup_map_injective Slot.indirect _ (fun _ _ eq => Slot.indirect.inj eq) inodeKeys
  have poolKeys : (pools state).Nodup := nodup_map_injective (fun b : Nat => Slot.pool b) _
    (fun _ _ eq => by have := Slot.pool.inj eq; omega) List.nodup_range
  have blocks : (dataSlots state).Nodup := by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro i _
      exact nodup_map_injective (Slot.data i) _ (fun _ _ eq => (Slot.data.inj eq).2)
        _root_.Std.ExtTreeMap.nodup_keys
    · apply inodeKeys.imp
      intro i j different x hx y hy same
      obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hy
      exact different (Slot.data.inj same).1
  simp only [family, List.nodup_cons, List.nodup_append, recs, blocks, inds, poolKeys,
    true_and, List.mem_cons, List.mem_append]
  simp only [records, indirects, List.mem_map, dataSlots_mem, pools_mem]
  grind

theorem footprintSpec : FootprintSpec where
  slice := fp_ok
  disjoint := fp_disjoint
  membership := family_mem
  nodup := family_nodup

end MachCSL.Logic.FsDurAlloc
