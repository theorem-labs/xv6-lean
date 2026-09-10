import MachCSL.Memory.Bytes

/-! Snapshot/submap properties needed by hart reservation preservation.
All widths and wraparound cases remain admitted. -/
namespace MachCSL.Memory

theorem insert_preserves_submap (left right : ByteMap width) (address : Address width)
    (byte : Byte) (sub : Submap left right) (lookup : right address = some byte) :
    Submap (insert left address byte) right := by
  intro other value h
  by_cases he : other = address
  · subst other
    simp only [insert_same, Option.some.injEq] at h
    simpa only [← h] using lookup
  · rw [insert_other left address other byte he] at h
    exact sub other value h

theorem writeOffsets_submap (left right : ByteMap width) (address : Address width)
    (value : BitVec bits) (offsets : List Nat) (sub : Submap left right)
    (reads : ∀ j ∈ offsets, right (addressAdd address j) = some (nthByte value j)) :
    Submap (writeOffsets left address value offsets) right := by
  induction offsets with
  | nil => exact sub
  | cons j rest ih =>
    apply insert_preserves_submap _ _ _ _
    · exact ih (fun i hi => reads i (by simp [hi]))
    · exact reads j (by simp)

/-- Any full bytewise read makes the resulting snapshot agree with memory.
Repeated addresses caused by wrapping need no separate exclusion premise. -/
theorem snapshot_submap (memory : ByteMap width) (address : Address width)
    (n : Nat) (value : BitVec bits)
    (reads : ∀ j, j < n → memory (addressAdd address j) = some (nthByte value j)) :
    Submap (snapshot address n value) memory := by
  apply writeOffsets_submap empty memory address value (List.range n)
  · intro a b h
    simp [empty] at h
  · intro j hj
    exact reads j (List.mem_range.mp hj)

end MachCSL.Memory
