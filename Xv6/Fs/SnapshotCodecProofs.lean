import Xv6.Fs.DinodeBlockProofs

/-! Reverse byte codecs needed by `FsDurImg` §11a/b. These laws reconstruct
arbitrary input bytes, rather than only decoding values produced by an encoder. -/
namespace Xv6.Fs
open MachCSL.Memory

theorem leAt_byte (bytes : List Byte) (offset n j : Nat) (bound : j < n) :
    nthByte (BitVec.ofInt (8 * n) (leAt bytes offset n)) j =
      byteAt bytes (offset + j) := by
  unfold leAt
  rw [BitVec.ofInt_natCast]
  rw [nthByte_assemble_len (8 * n)
    ((List.range n).map fun k => byteAt bytes (offset + k)) j
    (by simp) (by simpa using bound)]
  simp

/-- Re-encoding the decoded record recovers all 64 input bytes. Extra bytes
after the record are ignored, exactly as by the source decoder. -/
theorem encode_decodeDinode_prefix (bytes : List Byte) (full : 64 ≤ bytes.length) :
    dinodeBytes (decodeDinode bytes) = bytes.take 64 := by
  apply List.ext_getElem
    (by rw [dinodeBytes_length _ (decodeDinode_wf _)]; simp [Nat.min_eq_left full])
  intro j hj hk
  have bound : j < 64 := by simpa [List.length_take, Nat.min_eq_left full] using hk
  have byte_eq : byteAt (dinodeBytes (decodeDinode bytes)) j = byteAt bytes j := by
    by_cases low : j < 12
    · have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨
          j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 := by omega
      rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact leAt_byte bytes 0 2 _ (by decide)
        | exact leAt_byte bytes 2 2 _ (by decide)
        | exact leAt_byte bytes 4 2 _ (by decide)
        | exact leAt_byte bytes 6 2 _ (by decide)
        | exact leAt_byte bytes 8 4 _ (by decide)
    · have index : (j - 12) / 4 < (decodeDinode bytes).addrs.length := by
        simp only [decodeDinode, List.length_map, List.length_range]
        omega
      have rem : (j - 12) % 4 < 4 := Nat.mod_lt _ (by decide)
      rw [show j = 12 + (4 * ((j - 12) / 4) + (j - 12) % 4) by omega,
        dinodeBytes_addrs, indirectBytes_byte _ _ _ index rem]
      simp only [decodeDinode, List.getElem_map, List.getElem_range]
      rw [leAt_byte bytes _ 4 _ rem]
      congr 1
      omega
  simpa only [byteAt, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem (show j < bytes.length by omega), Option.getD_some,
    List.getElem_take] using byte_eq

/-- The indirect-word codec covers every byte, including entries past EOF. -/
theorem indirectBytes_roundtrip (bytes : List Byte) (n : Nat)
    (full : bytes.length = 4 * n) :
    indirectBytes ((List.range n).map fun j => BitVec.ofInt 32 (leAt bytes (4 * j) 4)) =
      bytes := by
  apply List.ext_getElem (by simp [indirectBytes_length, full])
  intro j hj hk
  have index : j / 4 < ((List.range n).map fun j => BitVec.ofInt 32 (leAt bytes (4 * j) 4)).length := by
    simp only [List.length_map, List.length_range]
    omega
  have rem : j % 4 < 4 := Nat.mod_lt _ (by decide)
  have eq := indirectBytes_byte
    ((List.range n).map fun j => BitVec.ofInt 32 (leAt bytes (4 * j) 4))
    (j / 4) (j % 4) index rem
  simp only [List.getElem_map, List.getElem_range] at eq
  rw [leAt_byte bytes _ 4 _ rem] at eq
  rw [show 4 * (j / 4) + j % 4 = j by omega] at eq
  simpa only [byteAt, List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hk,
    Option.getD_some] using eq

/-- The source `diblk_bytes_split`, retaining an arbitrary list of records. -/
theorem inodeBlockBytes_split (records : List Dinode) (k : Nat)
    (wf : ∀ dn ∈ records, dn.WellFormed) (bound : k < records.length) :
    ∃ pre post, inodeBlockBytes records =
      pre ++ dinodeBytes (records[k]?.getD default) ++ post ∧ pre.length = 64 * k := by
  induction records generalizing k with
  | nil => simp at bound
  | cons dn rest ih =>
    cases k with
    | zero => exact ⟨[], inodeBlockBytes rest, rfl, rfl⟩
    | succ k =>
      obtain ⟨pre, post, equation, size⟩ := ih k (fun d h => wf d (by simp [h]))
        (by simpa using bound)
      refine ⟨dinodeBytes dn ++ pre, post, ?_, ?_⟩
      · simpa only [inodeBlockBytes, List.getElem?_cons_succ, List.append_assoc] using
          congrArg (dinodeBytes dn ++ ·) equation
      · rw [List.length_append, dinodeBytes_length dn (wf dn (by simp)), size]
        omega

end Xv6.Fs
