import MachCSL.Logic.FsDurBytesSpec

namespace MachCSL.Logic.FsDurBytes
open Iris Iris.Std MachCSL.Memory

theorem byteRun_lookup (start a : Int) (bytes : List Byte) (v : Byte) :
    (byteRun start bytes)[a]? = some v ↔
      ∃ k : Nat, bytes[k]? = some v ∧ a = start + (k : Int) := by
  change PartialMap.get? (M := Disk.ImageMap) (byteRun start bytes) a = some v ↔ _
  rw [← LawfulFiniteMap.toList_get]
  have perm := LawfulFiniteMap.toList_map_seqZ (M' := Disk.ImageMap) (start := start) (l := bytes)
  unfold byteRun
  rw [perm.mem_iff, List.mem_mapIdx]
  constructor
  · rintro ⟨k, hk, same⟩
    exact ⟨k, List.getElem?_eq_some_iff.mpr ⟨hk, congrArg Prod.snd same⟩, (congrArg Prod.fst same).symm⟩
  · rintro ⟨k, get, addr⟩
    obtain ⟨hk, hv⟩ := List.getElem?_eq_some_iff.mp get
    exact ⟨k, hk, Prod.ext addr.symm hv⟩

theorem byteRun_empty start : byteRun start [] = ∅ := rfl

theorem leftUnion_lookup (left right : ByteMap) (a : Int) :
    (leftUnion left right)[a]? = left[a]?.orElse (fun _ => right[a]?) :=
  LawfulPartialMap.get?_union (M := Disk.ImageMap)

theorem flattenList_empty : flattenList [] = ∅ := rfl
theorem flattenList_cons (b : Int) (bytes : List Byte) rest :
    flattenList ((b, bytes) :: rest) = leftUnion (byteRun (b * 1024) bytes) (flattenList rest) := rfl

/-- Stride arithmetic does not restrict block numbers to nonnegative values. -/
theorem block_byte_unique (b c : Int) (bytes other : List Byte) (k j : Nat) (v w : Byte)
    (len : bytes.length ≤ 1024) (olen : other.length ≤ 1024)
    (get : bytes[k]? = some v) (oget : other[j]? = some w)
    (same : b * 1024 + (k : Int) = c * 1024 + (j : Int)) : b = c ∧ k = j := by
  have hk := (List.getElem?_eq_some_iff.mp get).1
  have hj := (List.getElem?_eq_some_iff.mp oget).1
  constructor <;> omega

theorem flattenList_lookup (entries : List (Int × List Byte))
    (bounded : ∀ b bytes, (b, bytes) ∈ entries → bytes.length ≤ 1024)
    (functional : ∀ b bytes other, (b, bytes) ∈ entries → (b, other) ∈ entries → bytes = other)
    (a : Int) (v : Byte) :
    (flattenList entries)[a]? = some v ↔
      ∃ (b : Int) (bytes : List Byte) (k : Nat),
        (b, bytes) ∈ entries ∧ bytes[k]? = some v ∧ a = b * 1024 + (k : Int) := by
  induction entries with
  | nil => simp [flattenList]
  | cons entry rest ih =>
    obtain ⟨b, bytes⟩ := entry
    have boundRest : ∀ c other, (c, other) ∈ rest → other.length ≤ 1024 :=
      fun c other mem => bounded c other (.tail _ mem)
    have funRest : ∀ c other third, (c, other) ∈ rest → (c, third) ∈ rest → other = third :=
      fun c other third h1 h2 => functional c other third (.tail _ h1) (.tail _ h2)
    have tailEq := ih boundRest funRest
    rw [flattenList_cons, leftUnion_lookup]
    constructor
    · intro found
      cases head : (byteRun (b * 1024) bytes)[a]? with
      | none =>
        rw [head, Option.orElse_none] at found
        obtain ⟨c, other, k, mem, get, addr⟩ := (tailEq.mp found)
        exact ⟨c, other, k, .tail _ mem, get, addr⟩
      | some value =>
        rw [head, Option.orElse_some] at found
        cases found
        obtain ⟨k, get, addr⟩ := (byteRun_lookup _ _ _ _).mp head
        exact ⟨b, bytes, k, .head _, get, addr⟩
    · rintro ⟨c, other, k, mem, get, addr⟩
      rcases List.mem_cons.mp mem with same | mem
      · cases same
        have head := (byteRun_lookup (b * 1024) a bytes v).mpr ⟨k, get, addr⟩
        rw [head, Option.orElse_some]
      · have tail := tailEq.mpr ⟨c, other, k, mem, get, addr⟩
        cases head : (byteRun (b * 1024) bytes)[a]? with
        | none => rw [Option.orElse_none]; exact tail
        | some value =>
          obtain ⟨j, hget, haddr⟩ := (byteRun_lookup _ _ _ _).mp head
          obtain ⟨sameBlock, sameIndex⟩ := block_byte_unique b c bytes other j k value v
            (bounded b bytes (.head _)) (boundRest c other mem) hget get (haddr.symm.trans addr)
          subst c
          have sameBytes := functional b bytes other (.head _) (.tail _ mem)
          subst other
          subst k
          have sameValue : value = v := Option.some.inj (hget.symm.trans get)
          rw [Option.orElse_some, sameValue]

theorem flatten_lookup (blocks : BlockMap) (a : Int) (v : Byte) (ok : DbytesOK blocks) :
    (flatten blocks)[a]? = some v ↔
      ∃ (b : Int) (bytes : List Byte) (k : Nat),
        blocks[b]? = some bytes ∧ bytes[k]? = some v ∧ a = b * 1024 + (k : Int) := by
  have getEq (b : Int) (bytes : List Byte) :
      (b, bytes) ∈ FiniteMap.toList (M := Disk.ImageMap) blocks ↔ blocks[b]? = some bytes :=
    LawfulFiniteMap.toList_get (M := Disk.ImageMap)
  have bounded : ∀ b bytes, (b, bytes) ∈ FiniteMap.toList (M := Disk.ImageMap) blocks → bytes.length ≤ 1024 :=
    fun b bytes mem => ok b bytes ((getEq b bytes).mp mem)
  have functional : ∀ b bytes other, (b, bytes) ∈ FiniteMap.toList (M := Disk.ImageMap) blocks →
      (b, other) ∈ FiniteMap.toList (M := Disk.ImageMap) blocks → bytes = other := by
    intro b bytes other h1 h2
    exact Option.some.inj (((getEq b bytes).mp h1).symm.trans ((getEq b other).mp h2))
  rw [flatten, flattenList_lookup _ bounded functional]
  simp only [getEq]

theorem map_eq_of_lookup (left right : ByteMap)
    (same : ∀ (a : Int) (v : Byte), left[a]? = some v ↔ right[a]? = some v) : left = right := by
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro a
  cases h1 : left[a]? with
  | none =>
    cases h2 : right[a]? with
    | none => rfl
    | some v =>
      have impossible := (same a v).mpr h2
      rw [h1] at impossible
      cases impossible
  | some v => exact ((same a v).mp h1).symm

theorem flatten_enumeration (blocks : BlockMap) (entries : List (Int × List Byte))
    (ok : DbytesOK blocks) (perm : entries.Perm (FiniteMap.toList (M := Disk.ImageMap) blocks)) :
    flattenList entries = flatten blocks := by
  have getEq (b : Int) (bytes : List Byte) : (b, bytes) ∈ entries ↔ blocks[b]? = some bytes :=
    perm.mem_iff.trans (LawfulFiniteMap.toList_get (M := Disk.ImageMap))
  have bounded : ∀ b bytes, (b, bytes) ∈ entries → bytes.length ≤ 1024 :=
    fun b bytes mem => ok b bytes ((getEq b bytes).mp mem)
  have functional : ∀ b bytes other, (b, bytes) ∈ entries → (b, other) ∈ entries → bytes = other := by
    intro b bytes other h1 h2
    exact Option.some.inj (((getEq b bytes).mp h1).symm.trans ((getEq b other).mp h2))
  apply map_eq_of_lookup
  intro a v
  rw [flattenList_lookup entries bounded functional, flatten_lookup blocks a v ok]
  simp only [getEq]

theorem dbytesOK_full (blocks : BlockMap) (full : BlocksFull blocks) : DbytesOK blocks :=
  fun b bytes found => Nat.le_of_eq (full b bytes found)

theorem dbytesOK_tail (blocks : BlockMap) b bytes (absent : blocks[b]? = none)
    (ok : DbytesOK (blocks.insert b bytes)) : DbytesOK blocks := by
  intro c other found
  apply ok c other
  have ne : b ≠ c := by intro same; subst c; rw [absent] at found; cases found
  simpa [_root_.Std.ExtTreeMap.getElem?_insert, ne] using found

theorem dbytesOK_head (blocks : BlockMap) b bytes (ok : DbytesOK (blocks.insert b bytes)) :
    bytes.length ≤ 1024 := ok b bytes (by simp)

theorem flatten_insert (blocks : BlockMap) b bytes (absent : blocks[b]? = none)
    (ok : DbytesOK (blocks.insert b bytes)) :
    flatten (blocks.insert b bytes) = leftUnion (byteRun (b * 1024) bytes) (flatten blocks) := by
  have bridge : PartialMap.insert (M := Disk.ImageMap) blocks b bytes = blocks.insert b bytes := by
    apply _root_.Std.ExtTreeMap.ext_getElem?
    intro c
    simp [PartialMap.insert, _root_.Std.ExtTreeMap.getElem?_alter, _root_.Std.ExtTreeMap.getElem?_insert]
  have perm := LawfulFiniteMap.toList_insert (M := Disk.ImageMap) (v := bytes) absent
  rw [bridge] at perm
  exact (flatten_enumeration (blocks.insert b bytes) ((b, bytes) :: FiniteMap.toList (M := Disk.ImageMap) blocks) ok perm.symm).symm

theorem byteRun_flatten_disjoint (blocks : BlockMap) b bytes (ok : DbytesOK blocks)
    (len : bytes.length ≤ 1024) (absent : blocks[b]? = none) :
    PartialMap.disjoint (M := Disk.ImageMap) (byteRun (b * 1024) bytes) (flatten blocks) := by
  apply (PartialMap.disjoint_iff _ _).mpr
  intro a
  cases head : (byteRun (b * 1024) bytes)[a]? with
  | none => exact Or.inl head
  | some v =>
    right
    cases tail : (flatten blocks)[a]? with
    | none => exact tail
    | some w =>
      obtain ⟨k, get, addr⟩ := (byteRun_lookup _ _ _ _).mp head
      obtain ⟨c, other, j, found, get', addr'⟩ := (flatten_lookup blocks a w ok).mp tail
      have same := (block_byte_unique b c bytes other k j v w len (ok c other found) get get'
        (addr.symm.trans addr')).1
      subst c
      rw [absent] at found
      cases found

theorem flatten_empty : flatten (∅ : BlockMap) = ∅ := rfl

theorem byteRun_cardinality start bytes : (byteRun start bytes).size = bytes.length := by
  have h := (LawfulFiniteMap.toList_map_seqZ (M' := Disk.ImageMap) (start := start) (l := bytes)).length_eq
  change (byteRun start bytes).toList.length = _ at h
  rw [_root_.Std.ExtTreeMap.length_toList, List.length_mapIdx] at h
  exact h

theorem negative_block_byte : (byteRun (-1024) [7#8])[-1024]? = some 7 :=
  (byteRun_lookup _ _ _ _).mpr ⟨0, rfl, by decide⟩

/-- The length guard is substantive: conflicting oversized blocks retain
an order-dependent result. No raw Rocq/Lean fold-order equality is claimed. -/
theorem malformed_order_matters :
    flattenList [(0, List.replicate 1025 (0#8)), (1, [1#8])] ≠
      flattenList [(1, [1#8]), (0, List.replicate 1025 (0#8))] := by
  have headA : (byteRun 0 (List.replicate 1025 (0#8)))[(1024 : Int)]? = some 0 :=
    (byteRun_lookup _ _ _ _).mpr ⟨1024, List.getElem?_replicate_of_lt (by decide), by decide⟩
  have headB : (byteRun 1024 [1#8])[(1024 : Int)]? = some 1 :=
    (byteRun_lookup _ _ _ _).mpr ⟨0, rfl, by decide⟩
  intro same
  have found := congrArg (fun bytes : ByteMap => bytes[(1024 : Int)]?) same
  simp only [flattenList_cons, Int.zero_mul, Int.one_mul, leftUnion_lookup,
    headA, headB, Option.orElse_some] at found
  have bad : (0#8) = (1#8) := Option.some.inj found
  exact (by decide : (0#8) ≠ (1#8)) bad

theorem flattenSpec : FlattenSpec where
  lookup := flatten_lookup
  enumeration := flatten_enumeration

end MachCSL.Logic.FsDurBytes
