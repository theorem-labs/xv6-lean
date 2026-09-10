import MachCSL.Memory.Proofs

/-! Byte writes and reservation footprints from `iris/RiscvModelBytes.v`
and `iris/RiscvLang.v` at the pinned paper revision. The right fold is
intentional: the first byte wins if an unbounded access wraps more than once.
No no-wrap or access-size premise is silently built into these definitions. -/
namespace MachCSL.Memory

def insert (m : ByteMap width) (a : Address width) (b : Byte) : ByteMap width :=
  overlay (singleton a b) m

def writeOffsets (m : ByteMap width) (a : Address width) (v : BitVec bits)
    (offsets : List Nat) : ByteMap width :=
  offsets.foldr (fun j acc => insert acc (addressAdd a j) (nthByte v j)) m

/-- Source `write_bytes`, with modular physical-address arithmetic. -/
def writeBytes (m : ByteMap width) (a : Address width) (n : Nat)
    (v : BitVec bits) : ByteMap width := writeOffsets m a v (List.range n)

def Footprint (a : Address width) (n : Nat) (b : Address width) : Prop :=
  ∃ j, j < n ∧ addressAdd a j = b

def snapshot (a : Address width) (n : Nat) (v : BitVec bits) : ByteMap width :=
  writeBytes empty a n v

def Domain (m : ByteMap width) (a : Address width) : Prop := ∃ b, m a = some b

def Submap (left right : ByteMap width) : Prop :=
  ∀ a b, left a = some b → right a = some b

def Disjoint (left right : Address width → Prop) : Prop :=
  ∀ a, left a → right a → False

@[simp] theorem insert_same (m : ByteMap width) (a : Address width) (b : Byte) :
    insert m a b a = some b := by simp [insert, overlay, singleton]

theorem insert_other (m : ByteMap width) (a other : Address width) (b : Byte)
    (h : other ≠ a) : insert m a b other = m other := by
  simp [insert, overlay, singleton, h]

theorem overlay_assoc (a b c : ByteMap width) :
    overlay a (overlay b c) = overlay (overlay a b) c := by
  funext x
  cases ha : a x <;> simp [overlay, ha]

@[simp] theorem overlay_empty_left (m : ByteMap width) : overlay empty m = m := by
  funext x
  simp [overlay, empty]

theorem writeOffsets_overlay (m : ByteMap width) (a : Address width)
    (v : BitVec bits) (offsets : List Nat) :
    writeOffsets m a v offsets = overlay (writeOffsets empty a v offsets) m := by
  induction offsets with
  | nil => simp [writeOffsets]
  | cons j js ih =>
    change insert (writeOffsets m a v js) (addressAdd a j) (nthByte v j) =
      overlay (insert (writeOffsets empty a v js) (addressAdd a j) (nthByte v j)) m
    rw [ih]
    exact overlay_assoc _ _ _

theorem writeBytes_overlay (m : ByteMap width) (a : Address width)
    (n : Nat) (v : BitVec bits) :
    writeBytes m a n v = overlay (snapshot a n v) m :=
  writeOffsets_overlay m a v (List.range n)

/-- Publishing a byte write preserves the flat-cache/log connection. -/
theorem flat_writeBytes (img : ByteMap width) (log : WriteLog width)
    (a : Address width) (n : Nat) (v : BitVec bits) (h : Agent) :
    flat img (log ++ [⟨snapshot a n v, h⟩]) = writeBytes (flat img log) a n v := by
  rw [flat_append, writeBytes_overlay]

private theorem writeOffsets_miss (m : ByteMap width) (a other : Address width)
    (v : BitVec bits) (offsets : List Nat)
    (h : ∀ j ∈ offsets, addressAdd a j ≠ other) :
    writeOffsets m a v offsets other = m other := by
  induction offsets with
  | nil => rfl
  | cons j js ih =>
    change insert (writeOffsets m a v js) (addressAdd a j) (nthByte v j) other = _
    rw [insert_other _ _ _ _ (Ne.symm (h j (by simp)))]
    exact ih (fun k hk => h k (by simp [hk]))

theorem writeBytes_outside (m : ByteMap width) (a other : Address width)
    (n : Nat) (v : BitVec bits) (h : ¬ Footprint a n other) :
    writeBytes m a n v other = m other := by
  apply writeOffsets_miss
  intro j hj he
  exact h ⟨j, List.mem_range.mp hj, he⟩

private theorem writeOffsets_domain (a other : Address width) (v : BitVec bits)
    (offsets : List Nat) :
    Domain (writeOffsets empty a v offsets) other ↔
      ∃ j ∈ offsets, addressAdd a j = other := by
  induction offsets with
  | nil => simp [writeOffsets, Domain, empty]
  | cons j js ih =>
    change Domain (insert (writeOffsets empty a v js) (addressAdd a j) (nthByte v j)) other ↔ _
    by_cases he : other = addressAdd a j
    · subst other
      simp [Domain, insert_same]
    · have hn : addressAdd a j ≠ other := Ne.symm he
      simpa [Domain, insert_other, he, hn] using ih

theorem snapshot_domain (a other : Address width) (n : Nat) (v : BitVec bits) :
    Domain (snapshot a n v) other ↔ Footprint a n other := by
  simpa [snapshot, writeBytes, Footprint] using
    writeOffsets_domain a other v (List.range n)

theorem writeBytes_preserves_submap (m reserved : ByteMap width) (a : Address width)
    (n : Nat) (v : BitVec bits) (hs : Submap reserved m)
    (hd : Disjoint (Footprint a n) (Domain reserved)) :
    Submap reserved (writeBytes m a n v) := by
  intro other b hb
  rw [writeBytes_outside m a other n v (fun hf => hd other hf ⟨b, hb⟩)]
  exact hs other b hb

end MachCSL.Memory
