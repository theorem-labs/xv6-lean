import MachCSL.Memory.Bytes

/-!
Little-endian byte assembly and partial memory reads, transcribed from
`iris/RiscvModelBytes.v:45–207` at xv6iris arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
The source nonnegative integer assembler is represented by `Nat`;
`Devices/MemoryBridge.lean` proves equality to the DMA integer assembler. Reads retain modular
addresses and fail if any byte is absent, without imposing a no-wrap premise.
-/
namespace MachCSL.Memory

/-- Source `assemble_bytes`, with a natural-number result. -/
def assembleBytes : List Byte → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * assembleBytes rest

/-- Source `read_bytes`: gather in increasing byte-offset order, then assemble. -/
def readBytes (memory : ByteMap width) (address : Address width) (n : Nat) :
    Option (BitVec (8 * n)) :=
  ((List.range n).mapM (fun j => memory (addressAdd address j))).map
    (fun bytes => BitVec.ofNat (8 * n) (assembleBytes bytes))

/-- Source `nth_byte_unsigned`. -/
theorem nthByte_unsigned (word : BitVec bits) (j : Nat) :
    (nthByte word j).toNat = (word.toNat / 2 ^ (8 * j)) % 256 := rfl

/-- Source `bv_eq_of_bytes`: all bytes determine a byte-aligned word. -/
theorem bv_eq_of_bytes (left right : BitVec (8 * n))
    (bytes : ∀ j, j < n → nthByte left j = nthByte right j) : left = right := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hb := congrArg (fun byte : Byte => byte.getLsbD (i % 8)) (bytes (i / 8) hj)
  have low : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have offset : 8 * (i / 8) + i % 8 = i := by omega
  simp only [nthByte, BitVec.getLsbD_ofNat, low, decide_true, Bool.true_and,
    ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight, offset] at hb
  exact hb

theorem assembleBytes_bound (bytes : List Byte) :
    assembleBytes bytes < 2 ^ (8 * bytes.length) := by
  induction bytes with
  | nil => decide
  | cons byte rest ih =>
    have hb : byte.toNat < 256 := byte.isLt
    change byte.toNat + 256 * assembleBytes rest < 2 ^ (8 * (rest.length + 1))
    rw [Nat.mul_succ, Nat.pow_add]
    change byte.toNat + 256 * assembleBytes rest < 2 ^ (8 * rest.length) * 256
    omega

theorem assembleBytes_byte (bytes : List Byte) (j : Nat) (hj : j < bytes.length) :
    (assembleBytes bytes / 2 ^ (8 * j)) % 256 = bytes[j].toNat := by
  induction bytes generalizing j with
  | nil => simp at hj
  | cons byte rest ih =>
    have hb : byte.toNat < 256 := byte.isLt
    cases j with
    | zero =>
      simp [assembleBytes, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
    | succ j =>
      have hj' : j < rest.length := by simpa using hj
      change ((byte.toNat + 256 * assembleBytes rest) / 2 ^ (8 * (j + 1))) % 256 = rest[j].toNat
      rw [show 8 * (j + 1) = 8 + 8 * j by omega, Nat.pow_add,
        ← Nat.div_div_eq_div_mul]
      change (((byte.toNat + 256 * assembleBytes rest) / 256) / 2 ^ (8 * j)) % 256 = _
      rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hb, Nat.zero_add]
      exact ih j hj'

/-- Source `nth_byte_assemble_len`, including words wider than the byte list. -/
theorem nthByte_assemble_len (bits : Nat) (bytes : List Byte) (j : Nat)
    (wide : 8 * bytes.length ≤ bits) (hj : j < bytes.length) :
    nthByte (BitVec.ofNat bits (assembleBytes bytes)) j = bytes[j] := by
  have bound : assembleBytes bytes < 2 ^ bits :=
    Nat.lt_of_lt_of_le (assembleBytes_bound bytes) (Nat.pow_le_pow_right (by decide) wide)
  apply BitVec.eq_of_toNat_eq
  simp only [nthByte_unsigned, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  exact assembleBytes_byte bytes j hj

private theorem mapM_some_spec (f : α → Option β) (xs : List α) (ys : List β)
    (h : xs.mapM f = some ys) :
    ys.length = xs.length ∧ ∀ j (hx : j < xs.length) (hy : j < ys.length),
      f xs[j] = some ys[j] := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst ys
    simp
  | cons x rest ih =>
    cases hy : f x with
    | none => simp [List.mapM_cons, hy] at h
    | some y =>
      cases ht : rest.mapM f with
      | none => simp [List.mapM_cons, hy, ht] at h
      | some tail =>
        have heq : y :: tail = ys := by simpa [List.mapM_cons, hy, ht] using h
        subst ys
        obtain ⟨length, lookup⟩ := ih tail ht
        refine ⟨by simp [length], ?_⟩
        intro j hx hy'
        cases j with
        | zero => exact hy
        | succ j => exact lookup j (by simpa using hx) (by simpa using hy')

private theorem mapM_some_of_lookup (f : α → Option β) (xs : List α) (ys : List β)
    (length : ys.length = xs.length)
    (lookup : ∀ j (hx : j < xs.length) (hy : j < ys.length), f xs[j] = some ys[j]) :
    xs.mapM f = some ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp length
    subst ys
    rfl
  | cons x rest ih =>
    cases ys with
    | nil => simp at length
    | cons y tail =>
      have head : f x = some y := lookup 0 (by simp) (by simp)
      have htail : rest.mapM f = some tail := ih tail (by simpa using length)
        (fun j hx hy => lookup (j + 1) (by simpa using hx) (by simpa using hy))
      simp [List.mapM_cons, head, htail]

/-- Source `read_bytes_spec`: every byte of a successful read came from memory. -/
theorem readBytes_spec (memory : ByteMap width) (address : Address width) (n : Nat)
    (word : BitVec (8 * n)) (h : readBytes memory address n = some word) :
    ∀ j, j < n → memory (addressAdd address j) = some (nthByte word j) := by
  unfold readBytes at h
  obtain ⟨bytes, gathered, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨length, lookup⟩ := mapM_some_spec
    (fun j => memory (addressAdd address j)) (List.range n) bytes gathered
  have hn : bytes.length = n := by simpa using length
  intro j hj
  have hb : j < bytes.length := by omega
  rw [nthByte_assemble_len (8 * n) bytes j (by omega) hb]
  have hlookup := lookup j (by simpa using hj) hb
  rw [List.getElem_range] at hlookup
  exact hlookup

/-- The converse also holds: any complete bytewise value is precisely the read. -/
theorem readBytes_of_bytes (memory : ByteMap width) (address : Address width) (n : Nat)
    (word : BitVec (8 * n))
    (bytes : ∀ j, j < n → memory (addressAdd address j) = some (nthByte word j)) :
    readBytes memory address n = some word := by
  let gathered := List.ofFn (fun i : Fin n => nthByte word i.val)
  have hlen : gathered.length = n := by simp [gathered]
  have hm : (List.range n).mapM (fun j => memory (addressAdd address j)) = some gathered := by
    apply mapM_some_of_lookup
    · simpa using hlen
    · intro j hj hg
      simpa [gathered] using bytes j (by simpa using hj)
  have assembled : BitVec.ofNat (8 * n) (assembleBytes gathered) = word := by
    apply bv_eq_of_bytes
    intro j hj
    have hg : j < gathered.length := by omega
    rw [nthByte_assemble_len (8 * n) gathered j (by omega) hg]
    simp [gathered]
  simp [readBytes, hm, assembled]

theorem readBytes_eq_some_iff (memory : ByteMap width) (address : Address width) (n : Nat)
    (word : BitVec (8 * n)) :
    readBytes memory address n = some word ↔
      ∀ j, j < n → memory (addressAdd address j) = some (nthByte word j) :=
  ⟨readBytes_spec memory address n word, readBytes_of_bytes memory address n word⟩

end MachCSL.Memory
