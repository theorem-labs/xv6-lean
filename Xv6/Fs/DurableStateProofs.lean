import Xv6.Fs.DurableImageNodeProofs

namespace Xv6.Fs.DurableState
open DurableImageNode

theorem metadata_superblock (s : State) : Metadata s 1 := Or.inl rfl

theorem metadata_bitmap (s : State) : Metadata s s.superblock.bmapstart := Or.inr (Or.inl rfl)

theorem metadata_inode (s : State) (i : Int) (n : DurableNode.Node)
    (lookup : s.inodes[i]? = some n) : Metadata s (s.superblock.inodestart + i / 16) :=
  Or.inr (Or.inr ⟨i, by simp [lookup], rfl⟩)

theorem geometry_inode_bounds (s : State) (h : Geometry s) (i : Int) (n : DurableNode.Node)
    (lookup : s.inodes[i]? = some n) :
    0 ≤ i ∧ i < 16 * (s.superblock.bmapstart - s.superblock.inodestart) := by
  have := h.region i n lookup
  constructor <;> omega

theorem geometry_metadata_distinct (s : State) (h : Geometry s) (i : Int) (n : DurableNode.Node)
    (lookup : s.inodes[i]? = some n) :
    1 ≠ s.superblock.inodestart + i / 16 ∧
    s.superblock.bmapstart ≠ s.superblock.inodestart + i / 16 := by
  have := h.region i n lookup
  have log := h.superblock.logstart
  have count := h.superblock.nlog
  have start := h.superblock.inodestart
  constructor <;> omega

theorem recordInBlock_nonnegative (bytes : List (BitVec 8)) (offset : Int) (record : Dinode)
    (h : RecordInBlock bytes offset record) : 0 ≤ offset := by
  obtain ⟨pre, post, eq, len⟩ := h
  omega

theorem recordInBlock_fits (bytes : List (BitVec 8)) (offset : Int) (record : Dinode)
    (wf : record.WellFormed) (h : RecordInBlock bytes offset record) :
    offset + 64 ≤ (bytes.length : Int) := by
  obtain ⟨pre, post, rfl, len⟩ := h
  simp only [List.length_append, dinodeBytes_length record wf]
  omega

theorem imageState_nib (h : BootImageWF disk ndisk sb nib cov) :
    (imageState (blocks disk) sb nib).nib = nib := by
  change (sb.ninodes / 16 + 1).toNat = nib
  rw [← h.rounded, Int.toNat_natCast]

theorem imageState_local (h : BootImageWF disk ndisk sb nib cov) :
    Local (imageState (blocks disk) sb nib) := by
  intro i n lookup
  obtain ⟨range, rfl⟩ := imageNodes_lookup_inv (blocks disk) sb nib i n lookup
  exact imageNode_local h i range

theorem imageState_geometry (h : BootImageWF disk ndisk sb nib cov) :
    Geometry (imageState (blocks disk) sb nib) where
  superblock := bootImage_superblock h
  region := by
    intro i n lookup
    obtain ⟨range, rfl⟩ := imageNodes_lookup_inv (blocks disk) sb nib i n lookup
    have endpoint := bootImage_region_end h
    change 0 ≤ i ∧ i / 16 < sb.bmapstart - sb.inodestart
    constructor <;> omega
  domain := by
    intro i bound
    change 0 ≤ i ∧ i < 16 * (sb.ninodes / 16 + 1) at bound
    change (imageNodes (blocks disk) sb nib)[i]?.isSome
    rw [imageNodes_lookup, if_pos (by have := h.rounded; exact ⟨bound.1, by omega⟩)]
    rfl
  directory := by
    intro i n lookup
    obtain ⟨range, rfl⟩ := imageNodes_lookup_inv (blocks disk) sb nib i n lookup
    rw [imageState_nib h]
    exact imageNode_dirLocal h i range

theorem imageState_all_inodes (image : Blocks) (sb : Superblock) (nib : Nat) (i : Int) :
    (imageState image sb nib).inodes[i]?.isSome ↔ 0 ≤ i ∧ i < 16 * (nib : Int) := by
  change (imageNodes image sb nib)[i]?.isSome ↔ _
  rw [imageNodes_lookup]
  split <;> simp_all

/-- All 208 rounded-region records are present for thirteen inode blocks,
including free records; no concrete image byte evaluation is needed. -/
theorem thirteen_blocks_domain (image : Blocks) (sb : Superblock) (i : Int) :
    (imageNodes image sb 13)[i]?.isSome ↔ 0 ≤ i ∧ i < 208 := by
  rw [imageNodes_lookup]
  split <;> simp_all

end Xv6.Fs.DurableState

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "Xv6.Fs.DurableNode." ||
        name.toString.startsWith "Xv6.Fs.DurableState." ||
        name.toString.startsWith "Xv6.Fs.DurableImageNode." ||
        name.toString.startsWith "_private.Xv6.Fs.Durable" then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} durable image-state declarations; standard foundational axioms only."
