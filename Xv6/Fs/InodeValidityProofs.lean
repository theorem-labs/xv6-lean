import Xv6.Fs.InodeValidityDefs
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace Xv6.Fs

theorem nblk_cover (size : Int) (_nonneg : 0 ≤ size) : size ≤ nblk size * 1024 := by
  unfold nblk
  omega

theorem nblocks_cover_nat (size : Int) (nonneg : 0 ≤ size) :
    size.toNat ≤ nblocks size * 1024 := by
  have cover := nblk_cover size nonneg
  unfold nblocks
  omega

theorem nblk_max (size : Int) (nonneg : 0 ≤ size) (cap : size ≤ 268 * 1024) :
    nblk size ≤ 268 := by
  unfold nblk
  omega

theorem nblk_lt (size k : Int) (_nonneg : 0 ≤ k) (inside : k * 1024 < size) :
    k < nblk size := by
  unfold nblk
  omega

theorem addrValid_iff (sb : Superblock) (address : Int) :
    addrValid sb address = true ↔ dataStart sb ≤ address ∧ address < sb.size := by
  simp [addrValid]

theorem inodeValid_iff (image : Blocks) (sb : Superblock) (dn : Dinode) :
    inodeValid image sb dn = true ↔ InodeOK image sb dn := by
  simp only [inodeValid, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨⟨⟨⟨ht, hn⟩, hs⟩, hd⟩, hi⟩, he⟩
    refine ⟨by simpa [or_assoc] using ht, hn, hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk hlt
      simpa [hlt, addrValid_iff] using hd k hk
    · intro k hk hge
      simpa [show ¬ (k : Int) < nblk dn.sizeZ by omega] using hd k hk
    · intro hle
      simpa [hle] using hi
    · intro hgt
      simpa [show ¬ nblk dn.sizeZ ≤ 12 by omega, addrValid_iff] using hi
    · intro j hj hlt
      simpa [hlt, addrValid_iff] using he j hj
    · intro j hj hge
      simpa [show ¬ (j : Int) < nblk dn.sizeZ - 12 by omega] using he j hj
  · intro h
    refine ⟨⟨⟨⟨⟨by simpa [or_assoc] using h.type, h.nlink⟩, h.size⟩, ?_⟩, ?_⟩, ?_⟩
    · intro k hk
      split
      · exact (addrValid_iff sb _).mpr (h.direct k hk ‹_›)
      · simpa using h.direct_zero k hk (by omega)
    · split
      · simpa using h.ind_zero ‹_›
      · exact (addrValid_iff sb _).mpr (h.ind (by omega))
    · intro j hj
      split
      · exact (addrValid_iff sb _).mpr (h.ent j hj ‹_›)
      · simpa using h.ent_zero j hj (by omega)

theorem inodeValid_ok (image : Blocks) (sb : Superblock) (dn : Dinode)
    (valid : inodeValid image sb dn = true) : InodeOK image sb dn :=
  (inodeValid_iff image sb dn).mp valid

theorem InodeOK.block (image : Blocks) (sb : Superblock) (dn : Dinode)
    (ok : InodeOK image sb dn) (k : Nat) (bound : k < 268)
    (inside : (k : Int) * 1024 < dn.sizeZ) :
    dataStart sb ≤ blockAddress image dn k ∧ blockAddress image dn k < sb.size := by
  have hn := nblk_lt dn.sizeZ (k : Int) (by omega) inside
  unfold blockAddress
  split
  · exact ok.direct k ‹_› hn
  · exact ok.ent (k - 12) (by omega) (by omega)

private theorem all_range_int (count : Nat) (check : Int → Bool) :
    (List.range count).all (fun i => check (i : Int)) = true ↔
      ∀ z : Int, 0 ≤ z ∧ z < (count : Int) → check z = true := by
  rw [List.all_eq_true]
  constructor
  · intro h z hz
    have hi : z.toNat < count := by omega
    have he : (z.toNat : Int) = z := by omega
    simpa only [he] using h z.toNat (List.mem_range.mpr hi)
  · intro h i hi
    exact h (i : Int) ⟨by omega, by have := List.mem_range.mp hi; omega⟩

theorem inodesValid_spec (image : Blocks) (sb : Superblock) (i : Int)
    (valid : inodesValid image sb = true) (bound : 0 ≤ i ∧ i < sb.ninodes)
    (live : (dinode image sb i).typeZ ≠ 0) : InodeOK image sb (dinode image sb i) := by
  have hi := (all_range_int sb.ninodes.toNat (fun z =>
    if (dinode image sb z).typeZ == 0 then true else inodeValid image sb (dinode image sb z))).mp valid i ⟨bound.1, by omega⟩
  apply inodeValid_ok
  simpa [live] using hi

theorem regionFree_spec (image : Blocks) (sb : Superblock) (nib : Nat) (z : Int)
    (free : regionFree image sb nib = true)
    (nonneg : 0 ≤ z) (tail : sb.ninodes ≤ z) (bound : z < 16 * (nib : Int)) :
    (dinode image sb z).typeZ = 0 := by
  have h := (all_range_int (16 * nib) (fun z =>
    if z < sb.ninodes then true else (dinode image sb z).typeZ == 0)).mp free z ⟨nonneg, by omega⟩
  simpa [show ¬ z < sb.ninodes by omega] using h

private theorem regionNlink_at (image : Blocks) (sb : Superblock) (nib : Nat) (z : Int)
    (checked : regionNlink image sb nib = true) (bound : 0 ≤ z ∧ z < 16 * (nib : Int)) :
    ((dinode image sb z).typeZ = 0 → (dinode image sb z).nlinkZ = 0) ∧
      (dinode image sb z).nlinkZ ≤ 32767 := by
  have h := (all_range_int (16 * nib) (fun z =>
    (if (dinode image sb z).typeZ == 0 then (dinode image sb z).nlinkZ == 0 else true) &&
      decide ((dinode image sb z).nlinkZ ≤ 32767))).mp checked z ⟨bound.1, by omega⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h.2⟩
  intro ht
  simpa [ht] using h.1

theorem regionNlink_free (image : Blocks) (sb : Superblock) (nib : Nat) (z : Int)
    (checked : regionNlink image sb nib = true) (bound : 0 ≤ z ∧ z < 16 * (nib : Int))
    (free : (dinode image sb z).typeZ = 0) : (dinode image sb z).nlinkZ = 0 :=
  (regionNlink_at image sb nib z checked bound).1 free

theorem regionNlink_short (image : Blocks) (sb : Superblock) (nib : Nat) (z : Int)
    (checked : regionNlink image sb nib = true) (bound : 0 ≤ z ∧ z < 16 * (nib : Int)) :
    (dinode image sb z).nlinkZ ≤ 32767 :=
  (regionNlink_at image sb nib z checked bound).2

theorem recordBare_iff (dn : Dinode) : recordBare dn = true ↔
    dn.sizeZ = 0 ∧ ∀ a ∈ dn.addrs, a.toNat = 0 := by
  simp [recordBare, List.all_eq_true]

/-- The default outside the arbitrary source address list is also zero. -/
theorem recordBare_addr (dn : Dinode) (bare : recordBare dn = true) (k : Nat) :
    dn.addrZ k = 0 := by
  have hb := (recordBare_iff dn).mp bare
  unfold Dinode.addrZ
  cases he : dn.addrs[k]? with
  | none => rfl
  | some a =>
    have hv := hb.2 a (List.mem_of_getElem? he)
    simp [hv]

private theorem regionBare_at (image : Blocks) (sb : Superblock) (nib : Nat) (z : Int)
    (checked : regionBare image sb nib = true) (bound : 0 ≤ z ∧ z < 16 * (nib : Int))
    (free : (dinode image sb z).typeZ = 0) : recordBare (dinode image sb z) = true := by
  have h := (all_range_int (16 * nib) (fun z =>
    if (dinode image sb z).typeZ == 0 then recordBare (dinode image sb z) else true)).mp checked z ⟨bound.1, by omega⟩
  simpa [free] using h

theorem regionBare_size (image : Blocks) (sb : Superblock) (nib : Nat) (z : Int)
    (checked : regionBare image sb nib = true) (bound : 0 ≤ z ∧ z < 16 * (nib : Int))
    (free : (dinode image sb z).typeZ = 0) : (dinode image sb z).sizeZ = 0 :=
  ((recordBare_iff _).mp (regionBare_at image sb nib z checked bound free)).1

theorem regionBare_addr (image : Blocks) (sb : Superblock) (nib : Nat) (z : Int) (k : Nat)
    (checked : regionBare image sb nib = true) (bound : 0 ≤ z ∧ z < 16 * (nib : Int))
    (free : (dinode image sb z).typeZ = 0) : (dinode image sb z).addrZ k = 0 :=
  recordBare_addr _ (regionBare_at image sb nib z checked bound free) k

theorem regionValid_iff (image : Blocks) (sb : Superblock) (nib : Nat) :
    regionValid image sb nib = true ↔
      regionFree image sb nib = true ∧ regionNlink image sb nib = true := by
  simp [regionValid]

theorem regionValid_free (image : Blocks) (sb : Superblock) (nib : Nat)
    (valid : regionValid image sb nib = true) : regionFree image sb nib = true :=
  ((regionValid_iff image sb nib).mp valid).1

theorem regionValid_nlink (image : Blocks) (sb : Superblock) (nib : Nat)
    (valid : regionValid image sb nib = true) : regionNlink image sb nib = true :=
  ((regionValid_iff image sb nib).mp valid).2

theorem liveInodes_mem (image : Blocks) (sb : Superblock) (z : Int) :
    z ∈ liveInodes image sb ↔
      (0 ≤ z ∧ z < sb.ninodes) ∧ (dinode image sb z).typeZ ≠ 0 := by
  simp only [liveInodes, List.mem_filter, List.mem_map, List.mem_range]
  simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
  constructor
  · rintro ⟨⟨i, hi, he⟩, live⟩
    change (i : Int) = z at he
    exact ⟨⟨by omega, by omega⟩, live⟩
  · rintro ⟨bound, live⟩
    exact ⟨⟨z.toNat, by omega, (show (z.toNat : Int) = z by omega)⟩, live⟩

theorem liveSet_mem (image : Blocks) (sb : Superblock) (z : Int) :
    z ∈ liveSet image sb ↔
      (0 ≤ z ∧ z < sb.ninodes) ∧ (dinode image sb z).typeZ ≠ 0 := by
  simpa [liveSet, Std.ExtTreeSet.mem_ofList, List.contains_iff_mem] using liveInodes_mem image sb z

/-- Together, the bounded inode sweep and whole-region tail check classify every
record in the rounded inode region, rather than only the advertised inode count. -/
theorem region_classify (image : Blocks) (sb : Superblock) (nib : Nat) (z : Int)
    (valid : inodesValid image sb = true) (tail : regionFree image sb nib = true)
    (bound : 0 ≤ z ∧ z < 16 * (nib : Int)) :
    (dinode image sb z).typeZ = 0 ∨
      (z ∈ liveSet image sb ∧ InodeOK image sb (dinode image sb z)) := by
  by_cases free : (dinode image sb z).typeZ = 0
  · exact Or.inl free
  · right
    have inside : z < sb.ninodes := by
      by_cases h : z < sb.ninodes
      · exact h
      · exact (free (regionFree_spec image sb nib z tail bound.1 (by omega) bound.2)).elim
    exact ⟨(liveSet_mem image sb z).mpr ⟨⟨bound.1, inside⟩, free⟩,
      inodesValid_spec image sb z valid ⟨bound.1, inside⟩ free⟩

/-- Read-only normalization for concrete image certificates; the modulo-32 inode
index and signed superblock block address stay explicit. -/
theorem dinode_type_blocks (disk : Disk) (sb : Superblock) (inum : Int) :
    (dinode (blocks disk) sb inum).type =
      BitVec.ofInt 16 (MachCSL.Memory.assembleBytes
        ((List.range 2).map fun j : Nat =>
          disk (inodeBlock (BitVec.ofInt 32 inum) sb.inodestart * 1024 +
            ((64 * inodeSlot (BitVec.ofInt 32 inum) + j : Nat) : Int))) : Int) := by
  change BitVec.ofInt 16 (leAt ((blocks disk
    (inodeBlock (BitVec.ofInt 32 inum) sb.inodestart)).drop
      (64 * inodeSlot (BitVec.ofInt 32 inum))) 0 2) = _
  unfold leAt
  congr 3
  apply List.map_congr_left
  intro j hj
  have slot := inodeSlot_lt (BitVec.ofInt 32 inum)
  have bound : 64 * inodeSlot (BitVec.ofInt 32 inum) + j < 1024 := by
    have := List.mem_range.mp hj
    omega
  rw [show byteAt ((blocks disk (inodeBlock (BitVec.ofInt 32 inum) sb.inodestart)).drop
      (64 * inodeSlot (BitVec.ofInt 32 inum))) (0 + j) =
      byteAt (blocks disk (inodeBlock (BitVec.ofInt 32 inum) sb.inodestart))
        (64 * inodeSlot (BitVec.ofInt 32 inum) + j) from by
          simp [byteAt, List.getElem?_drop]]
  exact blocks_byte disk _ _ bound

namespace InodeValidityTests

def freeWithGarbage : Dinode := ⟨0, 0, 0, 5, 4096, [7]⟩

theorem free_record_not_bare : recordBare freeWithGarbage = false := by decide

theorem unused_direct_rejected (image : Blocks) (sb : Superblock) :
    inodeValid image sb ⟨2, 0, 0, 1, 0, [7]⟩ = false := by
  rfl

theorem free_record_not_w3_live (image : Blocks) (sb : Superblock) :
    inodeValid image sb freeWithGarbage = false := by rfl

theorem negative_count_empty (image : Blocks) (sb : Superblock) (h : sb.ninodes ≤ 0) :
    inodesValid image sb = true := by
  have he : sb.ninodes.toNat = 0 := by omega
  simp [inodesValid, he]

theorem empty_region (image : Blocks) (sb : Superblock) :
    regionValid image sb 0 = true ∧ regionBare image sb 0 = true := by
  exact ⟨rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- W3 alone deliberately skips a type-zero record, even if its other fields
contain garbage. The separate region checks reject that same input. -/
theorem w3_skips_free_garbage (sb : Superblock) :
    inodesValid (fun _ => dinodeBytes freeWithGarbage) { sb with ninodes := 1 } = true := by
  rfl

set_option maxRecDepth 4096 in
theorem region_rejects_free_garbage (sb : Superblock) :
    regionNlink (fun _ => dinodeBytes freeWithGarbage) sb 1 = false ∧
    regionBare (fun _ => dinodeBytes freeWithGarbage) sb 1 = false := by
  have ht : (dinode (fun _ => dinodeBytes freeWithGarbage) sb 0).typeZ = 0 := by
    change (decodeDinode (dinodeBytes freeWithGarbage)).typeZ = 0
    decide
  have hn : (dinode (fun _ => dinodeBytes freeWithGarbage) sb 0).nlinkZ = 5 := by
    change (decodeDinode (dinodeBytes freeWithGarbage)).nlinkZ = 5
    decide
  have hs : (dinode (fun _ => dinodeBytes freeWithGarbage) sb 0).sizeZ = 4096 := by
    change (decodeDinode (dinodeBytes freeWithGarbage)).sizeZ = 4096
    decide
  constructor
  · cases he : regionNlink (fun _ => dinodeBytes freeWithGarbage) sb 1 with
    | false => rfl
    | true =>
      have h := regionNlink_free _ sb 1 0 he (by decide) ht
      rw [hn] at h
      contradiction
  · cases he : regionBare (fun _ => dinodeBytes freeWithGarbage) sb 1 with
    | false => rfl
    | true =>
      have h := regionBare_size _ sb 1 0 he (by decide) ht
      have : (4096 : Int) = 0 := hs.symm.trans h
      omega

end InodeValidityTests
end Xv6.Fs

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let text := name.toString
    if info.isTheorem && (text.startsWith "Xv6.Fs." || text.startsWith "_private.Xv6.Fs.") then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} filesystem theorem cones; standard foundational axioms only."
