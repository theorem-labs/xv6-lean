import Xv6.Fs.SnapshotDefs
import Xv6.Fs.DurableStateProofs
import MachCSL.Logic.FsLinkProofs

namespace Xv6.Fs.Snapshot
open DurableState DurableNode LinkFamily MachCSL.Logic.FsLink Iris Iris.CMRA

theorem ok_intro (bytes : Bytes state disk) (localOK : DurableState.Local state) : OK state disk :=
  ⟨bytes, localOK⟩
theorem ok_bytes (ok : OK state disk) : Bytes state disk := ok.1
theorem ok_local (ok : OK state disk) : DurableState.Local state := ok.2
theorem holds_intro (ok : OK state disk) : Holds disk := ⟨state, ok⟩

theorem bytes_geometry (bytes : Bytes state disk) : Geometry state :=
  ⟨bytes.superblockOK, bytes.region, bytes.regionDomain, bytes.directory⟩

theorem ok_geometry (ok : OK state disk) : Geometry state := bytes_geometry ok.1
theorem ok_shape (ok : OK state disk) : Shape state disk := ⟨ok.1.domainBelow⟩

theorem bytes_inode_read (bytes : Bytes state disk) (i : Int) (n : Node)
    (found : state.inodes[i]? = some n) : InodeRead state.superblock disk i n :=
  ⟨bytes.record i n found, fun k bs hk => bytes.data i n k bs found hk,
    bytes.indirect i n found, bytes.slot i n found⟩

theorem bytes_directory_width (bytes : Bytes state disk) (i : Int) (n : Node) (nib : Nat)
    (found : state.inodes[i]? = some n) (width : (nib : Int) = state.superblock.ninodes / 16 + 1) :
    DirLocal i nib n := by
  have same : state.nib = nib := by
    rw [State.nib, ← width, Int.toNat_natCast]
  rw [← same]
  exact bytes.directory i n found

theorem bytes_links_plain (bytes : Bytes state disk) :
    ∃ f, ElemOK state.inodes f ∧ ✓ elem state.inodes f := by
  obtain ⟨f, value, ok, valid⟩ := bytes.links
  exact ⟨f, ok, CMRA.valid_op_left valid⟩

theorem metadata_distinct (bytes : Bytes state disk) (i : Int) (n : Node)
    (found : state.inodes[i]? = some n) :
    1 ≠ state.superblock.inodestart + i / 16 ∧
      state.superblock.bmapstart ≠ state.superblock.inodestart + i / 16 :=
  geometry_metadata_distinct state (bytes_geometry bytes) i n found

theorem superblock_bitmap_distinct (bytes : Bytes state disk) : (1 : Int) ≠ state.superblock.bmapstart := by
  have geom := bytes.superblockOK
  have := geom.logstart
  have := geom.nlog
  have := geom.inodestart
  have := geom.bmapstart
  have := geom.ninodes
  omega

theorem free_not_metadata (bytes : Bytes state disk) (b : Int) (free : b ∉ state.used) :
    ¬Metadata state b := fun isMeta => free (bytes.metadataUsed b isMeta)

theorem free_not_owned (bytes : Bytes state disk) (i : Int) (n : Node) (b : Int)
    (found : state.inodes[i]? = some n) (free : b ∉ state.used) : ¬n.Owns b :=
  fun own => free (bytes.ownedUsed i n b found own).1

theorem distinct_nodes_disjoint (bytes : Bytes state disk) (i : Int) (n : Node) (j : Int) (m : Node)
    (left : state.inodes[i]? = some n) (right : state.inodes[j]? = some m) (different : i ≠ j) :
    ∀ b, n.Owns b → ¬m.Owns b :=
  fun b hn hm => different (bytes.disjoint i n j m b left right hn hm)

theorem record_slot_fits (bytes : Bytes state disk) (i : Int) (n : Node)
    (found : state.inodes[i]? = some n) :
    ∃ block, disk[state.superblock.inodestart + i / 16]? = some block ∧
      RecordInBlock block (64 * (i % 16)) n.record ∧
      0 ≤ 64 * (i % 16) ∧ 64 * (i % 16) + 64 ≤ 1024 := by
  obtain ⟨block, lookup, record⟩ := bytes.record i n found
  have size := bytes.blockSize _ _ lookup
  have fits := recordInBlock_fits block _ n.record (bytes.repr i n found).record record
  exact ⟨block, lookup, record, recordInBlock_nonnegative block _ _ record, by omega⟩

theorem data_block_sized (bytes : Bytes state disk) (i : Int) (n : Node) (k : Nat) block
    (found : state.inodes[i]? = some n) (data : n.blocks[k]? = some block) : block.length = 1024 :=
  bytes.blockSize _ _ (bytes.data i n k block found data)

theorem data_block_real (bytes : Bytes state disk) (i : Int) (n : Node) (k : Nat) block
    (found : state.inodes[i]? = some n) (data : n.blocks[k]? = some block) :
    0 ≤ n.address k ∧ n.address k < state.superblock.size := by
  exact bytes.domainBelow _ (by rw [bytes.data i n k block found data]; rfl)

theorem negative_block_absent (bytes : Bytes state disk) (b : Int) (negative : b < 0) : disk[b]? = none := by
  cases found : disk[b]?
  · rfl
  · have := bytes.domainBelow b (by rw [found]; rfl)
    omega

theorem oversized_block_absent (bytes : Bytes state disk) (b : Int) (outside : state.superblock.size ≤ b) :
    disk[b]? = none := by
  cases found : disk[b]?
  · rfl
  · have := bytes.domainBelow b (by rw [found]; rfl)
    omega

/-- The source contract allows block zero in the finite map. Its pool
obligation includes zero whenever its bit is free; positivity is not added. -/
theorem free_zero_present (bytes : Bytes state disk) (free : (0 : Int) ∉ state.used) : disk[(0 : Int)]?.isSome := by
  have := superblock_metadata state.superblock bytes.superblockOK
  have := bytes.superblockOK.logstart
  have := bytes.superblockOK.nlog
  have := bytes.superblockOK.inodestart
  exact bytes.pool 0 ⟨by omega, by omega⟩ free

end Xv6.Fs.Snapshot

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "Xv6.Fs.Snapshot." || name.toString.startsWith "_private.Xv6.Fs.Snapshot" then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} snapshot declarations; standard foundational axioms only."
