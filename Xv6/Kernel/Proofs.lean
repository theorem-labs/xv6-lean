import Xv6.Kernel.Defs
import Init.Data.Nat.Mod

namespace Xv6.Kernel

theorem listMap_append {α : Type} (left right : List (Int × α)) (a : Int) :
    listMap (left ++ right) a = (listMap left a).orElse (fun _ => listMap right a) := by
  induction left with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨k, v⟩
    simp only [List.cons_append, listMap]
    split <;> simp_all

private theorem listMap_consecutive (base a : Int) (offset count : Nat) (byte : Nat → UInt8) :
    listMap ((List.range count).map (fun i => (base + (offset + i : Nat), byte (offset + i)))) a =
      if base + offset ≤ a ∧ a < base + (offset + count : Nat) then
        some (byte (a - base).toNat) else none := by
  induction count generalizing offset with
  | zero => simp [listMap]
  | succ count ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero, listMap, Function.comp_def, Nat.succ_eq_add_one]
    have he : (fun x => (base + (offset + (x + 1) : Nat), byte (offset + (x + 1)))) =
        (fun x => (base + (offset + 1 + x : Nat), byte (offset + 1 + x))) := by
      funext x; congr 2 <;> omega
    rw [he, ih]
    repeat' split
    all_goals simp_all
    all_goals try omega
    congr 2; omega

theorem ByteRun.lookup_eq_listMap (run : ByteRun) (a : Int) :
    run.lookup a = listMap run.entries a := by
  have h := listMap_consecutive run.base a 0 run.length run.byte
  simp only [Nat.zero_add, Int.natCast_zero, Int.add_zero] at h
  rw [ByteRun.entries, h]
  simp only [ByteRun.lookup]
  have he : (0 ≤ a - run.base ∧ a - run.base < (run.length : Int)) ↔
      (run.base ≤ a ∧ a < run.base + run.length) := by omega
  simp only [he]

theorem runMap_eq_listMap (runs : List ByteRun) (a : Int) :
    runMap runs a = listMap (runs.flatMap ByteRun.entries) a := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
    simp only [runMap, List.foldr_cons, List.flatMap_cons, listMap_append, Elf.union]
    rw [run.lookup_eq_listMap]
    exact congrArg (fun x => (listMap run.entries a).orElse (fun _ => x)) ih

/-- Truncating a word above the requested byte leaves that byte unchanged. -/
theorem truncated_byte (word count i : Nat) (hi : i < count) :
    ((word % 2 ^ (8 * count)) >>> (8 * i)) % 256 = (word >>> (8 * i)) % 256 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have he : 2 ^ (8 * count) = 2 ^ (8 * i) * (256 * 2 ^ (8 * (count - i - 1))) := by
    have hp : 8 * count = 8 * i + (8 + 8 * (count - i - 1)) := by omega
    rw [hp, Nat.pow_add, Nat.pow_add]
  rw [he, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

/-- A single arithmetic slice certificate covers every byte in a run. -/
theorem slice_byte (word payload offset count i : Nat)
    (certificate : payload = (word >>> (8 * offset)) % 2 ^ (8 * count))
    (hi : i < count) :
    ((payload >>> (8 * i)) % 256).toUInt8 =
      ((word >>> (8 * (offset + i))) % 256).toUInt8 := by
  rw [certificate, truncated_byte _ _ _ hi, ← Nat.shiftRight_add]
  congr 3; omega

end Xv6.Kernel

namespace Xv6.Kernel

/-- Arithmetic page slice certificates imply actual bounded packed reads. -/
theorem ByteRun.slice_read (run : ByteRun) (file : Image.Packed)
    (page offset : Nat) (word : Nat)
    (hp : file.pages[page]? = some word)
    (hw : offset + run.length ≤ 4096)
    (hb : page * 4096 + offset + run.length ≤ file.byteLength)
    (cert : run.payload = (word >>> (8 * offset)) % 2 ^ (8 * run.length))
    (i : Nat) (hi : i < run.length) :
    file.getByte? (page * 4096 + offset + i) = some (run.byte i) := by
  have hind : page * 4096 + offset + i < file.byteLength := by omega
  have hdiv : (page * 4096 + offset + i) / 4096 = page := by omega
  have hmod : (page * 4096 + offset + i) % 4096 = offset + i := by omega
  simp only [Image.Packed.getByte?, if_pos hind, hdiv, hmod, hp, Option.map_some]
  exact congrArg some (slice_byte word run.payload offset run.length i cert hi).symm

theorem ByteRun.lookup_some_iff (run : ByteRun) (a : Int) (b : UInt8) :
    run.lookup a = some b ↔
      run.base ≤ a ∧ a < run.base + run.length ∧ run.byte (a - run.base).toNat = b := by
  simp only [ByteRun.lookup]
  split <;> simp_all <;> omega

theorem runMap_some_exists (runs : List ByteRun) (a : Int) (b : UInt8)
    (h : runMap runs a = some b) : ∃ run ∈ runs, run.lookup a = some b := by
  induction runs with
  | nil => simp [runMap] at h
  | cons run rest ih =>
    simp only [runMap, List.foldr_cons, Elf.union] at h
    cases hr : run.lookup a with
    | none => exact (ih (by simpa [hr, runMap] using h)).imp fun r h => ⟨by simp [h.1], h.2⟩
    | some v => exact ⟨run, by simp, by simpa [hr, runMap] using h⟩

theorem runMap_defined_iff (runs : List ByteRun) (a : Int) :
    (∃ b, runMap runs a = some b) ↔
      ∃ run ∈ runs, run.base ≤ a ∧ a < run.base + run.length := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨run, hm, he⟩ := runMap_some_exists runs a b hb
    exact ⟨run, hm, (run.lookup_some_iff a b).mp he |>.1,
      (run.lookup_some_iff a b).mp he |>.2.1⟩
  · intro h
    induction runs with
    | nil => simp at h
    | cons run rest ih =>
      simp only [runMap, List.foldr_cons, Elf.union]
      cases he : run.lookup a with
      | some b => exact ⟨b, rfl⟩
      | none =>
        obtain ⟨r, hr, hlo, hhi⟩ := h
        rcases List.mem_cons.mp hr with hr | hr
        · subst r
          have ht := (run.lookup_some_iff a (run.byte (a - run.base).toNat)).mpr ⟨hlo, hhi, rfl⟩
          simp [he] at ht
        · exact ih ⟨r, hr, hlo, hhi⟩

theorem runMap_append (left right : List ByteRun) (a : Int) :
    runMap (left ++ right) a = Elf.union (runMap left) (runMap right) a := by
  simp only [runMap_eq_listMap, List.flatMap_append, listMap_append, Elf.union]

end Xv6.Kernel
