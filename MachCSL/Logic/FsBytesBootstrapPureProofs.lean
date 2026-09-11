import MachCSL.Logic.FsBytesBootstrapSpec
import MachCSL.Logic.FsDurBytesProofs

namespace MachCSL.Logic.FsBytesBootstrap
open Iris Iris.Std
open FsDurBytes FsBytesInvariant

theorem union_lookup {V : Type} (left right : Disk.ImageMap V) (a : Int) :
    get? (PartialMap.union left right) a = (get? left a).orElse (fun _ => get? right a) :=
  LawfulPartialMap.get?_union (M := Disk.ImageMap)

/-- The source filter helper is polymorphic in the map payload, not just bytes. -/
theorem filter_partition {V : Type} (map : FsBlockGhost.BlockMap V) (home : BlockSet) :
    let inside := PartialMap.filter (fun b (_ : V) => decide (b ∈ home)) map
    let outside := PartialMap.filter (fun b (_ : V) => decide (b ∉ home)) map
    PartialMap.union inside outside = map ∧ PartialMap.disjoint inside outside := by
  dsimp only
  have lookup (b : Int) :
      get? (PartialMap.filter (fun b (_ : V) => decide (b ∈ home)) map) b =
        if b ∈ home then get? map b else none := by
    rw [LawfulPartialMap.get?_filter]
    by_cases h : b ∈ home <;> simp [h]
  have lookup' (b : Int) :
      get? (PartialMap.filter (fun b (_ : V) => decide (b ∉ home)) map) b =
        if b ∈ home then none else get? map b := by
    rw [LawfulPartialMap.get?_filter]
    by_cases h : b ∈ home <;> simp [h]
  constructor
  · apply LawfulPartialMap.equiv_iff_eq.mp
    intro b
    rw [union_lookup, lookup, lookup']
    by_cases h : b ∈ home <;> simp [h]
  · intro b
    rw [lookup, lookup']
    by_cases h : b ∈ home <;> simp [h]

theorem fs_filter_dom {V : Type} (map : FsBlockGhost.BlockMap V) (home : BlockSet)
    (sub : home ⊆ FiniteMap.dom_set (S := BlockSet) map) :
    FiniteMap.dom_set (S := BlockSet)
      (PartialMap.filter (fun b (_ : V) => decide (b ∈ home)) map) = home := by
  apply LawfulSet.ext
  intro b
  rw [LawfulFiniteMap.mem_dom_set, LawfulPartialMap.get?_filter]
  by_cases h : b ∈ home
  · simpa [h] using LawfulFiniteMap.mem_dom_set.mp (sub b h)
  · simp [h]

theorem valueMap_lookup (cache : BlockMap) values b :
    get? (valueMap cache values) b = (get? cache b).map (fun _ => values b) := by
  simp only [valueMap, get?_bindAlter]
  cases get? cache b <;> rfl

theorem valueMap_domain (cache : BlockMap) values :
    FiniteMap.dom_set (S := BlockSet) (valueMap cache values) = FiniteMap.dom_set (S := BlockSet) cache := by
  apply LawfulSet.ext
  intro b
  simp only [LawfulFiniteMap.mem_dom_set, valueMap_lookup, Option.isSome_map]

theorem valueMap_full (cache : BlockMap) values
    (full : ∀ b, b ∈ FiniteMap.dom_set (S := BlockSet) cache → (values b).length = 1024) :
    BlocksFull (valueMap cache values) := by
  intro b bs found
  change get? (valueMap cache values) b = some bs at found
  rw [valueMap_lookup] at found
  obtain ⟨raw, hr, hv⟩ := Option.map_eq_some_iff.mp found
  subst bs
  exact full b (LawfulFiniteMap.mem_dom_set.mpr (by rw [hr]; rfl))

theorem homeMap_lookup (cache : BlockMap) home b :
    get? (homeMap cache home) b = if b ∈ home then get? cache b else none := by
  simp only [homeMap, LawfulPartialMap.get?_filter]
  by_cases h : b ∈ home <;> simp [h]

theorem outsideMap_lookup (cache : BlockMap) home b :
    get? (outsideMap cache home) b = if b ∈ home then none else get? cache b := by
  simp only [outsideMap, LawfulPartialMap.get?_filter]
  by_cases h : b ∈ home <;> simp [h]

theorem homeMap_get (cache : BlockMap) home b bs :
    get? (homeMap cache home) b = some bs ↔ get? cache b = some bs ∧ b ∈ home := by
  rw [homeMap_lookup]
  by_cases h : b ∈ home <;> simp [h]

theorem filter_union (cache : BlockMap) home :
    PartialMap.union (homeMap cache home) (outsideMap cache home) = cache := by
  apply LawfulPartialMap.equiv_iff_eq.mp
  intro b
  rw [union_lookup, homeMap_lookup, outsideMap_lookup]
  by_cases h : b ∈ home <;> simp [h]

theorem filter_disjoint (cache : BlockMap) home :
    PartialMap.disjoint (homeMap cache home) (outsideMap cache home) := by
  intro b
  rw [homeMap_lookup, outsideMap_lookup]
  by_cases h : b ∈ home <;> simp [h]

theorem homeMap_domain (cache : BlockMap) home
    (sub : home ⊆ FiniteMap.dom_set (S := BlockSet) cache) :
    FiniteMap.dom_set (S := BlockSet) (homeMap cache home) = home := by
  apply LawfulSet.ext
  intro b
  rw [LawfulFiniteMap.mem_dom_set, homeMap_lookup]
  by_cases h : b ∈ home
  · simp only [h, if_true, iff_true]
    exact LawfulFiniteMap.mem_dom_set.mp (sub b h)
  · simp [h]

theorem homeMap_full (cache : BlockMap) home (full : BlocksFull cache) : BlocksFull (homeMap cache home) := by
  intro b bs found
  exact full b bs ((homeMap_get cache home b bs).mp found).1

theorem flatten_domain (cache : BlockMap) (full : BlocksFull cache) :
    bytes_dom (flatten cache) (FiniteMap.dom_set (S := BlockSet) cache) := by
  intro a
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨b, bs, k, hb, hk, ha⟩ := (flatten_lookup cache a v (dbytesOK_full cache full)).mp hv
    have len := full b bs hb
    have bound := (List.getElem?_eq_some_iff.mp hk).1
    exact ⟨b, LawfulFiniteMap.mem_dom_set.mpr (by rw [show get? cache b = some bs from hb]; rfl), by omega, by omega⟩
  · rintro ⟨b, hb, lo, hi⟩
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp (LawfulFiniteMap.mem_dom_set.mp hb)
    let k := (a - b * 1024).toNat
    have addr : a = b * 1024 + (k : Int) := by dsimp [k]; omega
    have bound : k < bs.length := by rw [full b bs hbs]; dsimp [k]; omega
    apply Option.isSome_iff_exists.mpr
    exact ⟨bs[k], (flatten_lookup cache a bs[k] (dbytesOK_full cache full)).mpr
      ⟨b, bs, k, hbs, List.getElem?_eq_getElem bound, addr⟩⟩

theorem flatten_tie (cache : BlockMap) (full : BlocksFull cache) : bytes_tie (flatten cache) cache := by
  intro b bs hb a v ha
  obtain ⟨k, hk, addr⟩ := (byteRun_lookup (b * 1024) a bs v).mp ha
  exact (flatten_lookup cache a v (dbytesOK_full cache full)).mpr ⟨b, bs, k, hb, hk, addr⟩

theorem flatten_fresh (cache : BlockMap) (old : ByteMap) (home : BlockSet)
    (full : BlocksFull cache)
    (fresh : ∀ b, b ∈ FiniteMap.dom_set (S := BlockSet) cache → b ∉ home)
    (domain : bytes_dom old home) : PartialMap.disjoint (flatten cache) old := by
  intro a ⟨hc, ho⟩
  obtain ⟨b, hb, lo, hi⟩ := (flatten_domain cache full a).mp hc
  obtain ⟨c, hc, clo, chi⟩ := (domain a).mp ho
  have same : b = c := by omega
  exact fresh b hb (same ▸ hc)

theorem union_domain (left right : ByteMap) (lh rh : BlockSet)
    (hl : bytes_dom left lh) (hr : bytes_dom right rh) :
    bytes_dom (PartialMap.union left right) (rh ∪ lh) := by
  intro a
  rw [union_lookup]
  have option (l r : Option (BitVec 8)) :
      (l.orElse (fun _ => r)).isSome = (l.isSome || r.isSome) := by cases l <;> rfl
  rw [option, Bool.or_eq_true, hl a, hr a]
  constructor
  · rintro (⟨b, hb, lo, hi⟩ | ⟨b, hb, lo, hi⟩)
    · exact ⟨b, LawfulSet.mem_union.mpr (Or.inr hb), lo, hi⟩
    · exact ⟨b, LawfulSet.mem_union.mpr (Or.inl hb), lo, hi⟩
  · rintro ⟨b, hb, lo, hi⟩
    rcases LawfulSet.mem_union.mp hb with hb | hb
    · exact Or.inr ⟨b, hb, lo, hi⟩
    · exact Or.inl ⟨b, hb, lo, hi⟩

theorem union_tie (left right : ByteMap) (cache : BlockMap) (tie : bytes_tie left cache) :
    bytes_tie (PartialMap.union left right) cache := by
  intro b bs hb a v ha
  rw [union_lookup, tie b bs hb a v ha]
  rfl

theorem empty_domain : bytes_dom (∅ : ByteMap) (∅ : BlockSet) := by
  intro a
  simp [get?_empty]

end MachCSL.Logic.FsBytesBootstrap
