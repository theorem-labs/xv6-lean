import Xv6.Fs.SnapshotHomeDefs

/-! Exact total header decode and ordered replay from LogDefs43–67/155–164
and FsCrash349–354/460–464/844–850, at the pinned arxiv-v1 source. -/
namespace Xv6.Fs.Recovery
open MachCSL.Memory

abbrev BlockMap := DurableState.BlockMap

/-- A short header assembles only its available bytes. -/
def headerN (bytes : List Byte) : Int := assembleBytes (bytes.take 4)

def headerWord (bytes : List Byte) (i : Nat) : Int :=
  assembleBytes ((bytes.drop (4 * i)).take 4)

/-- The source decoder is unbounded; HeaderWF separately limits legal counts.
Missing words decode to zero by assembling the empty list. -/
def headerDecode (bytes : List Byte) : Nat × List Int :=
  let n := (headerWord bytes 0).toNat
  (n, (List.range n).map fun i => headerWord bytes (i + 1))

def installStep (physical : Blocks) (start : Int) (writes : List Int)
    (i : Nat) (disk : BlockMap) : BlockMap :=
  match writes[i]? with
  | some b => disk.insert b (physical (SnapshotHome.logSlot start i))
  | none => disk

/-- Right-folding indices preserves the source's first-index winner for
repeated destinations, even when no well-formedness predicate holds. -/
def install (physical : Blocks) (start : Int) (writes : List Int)
    (disk : BlockMap) : BlockMap :=
  (List.range writes.length).foldr (installStep physical start writes) disk

def recover (physical : Blocks) (coverage : BlockSet) (start : Int) : BlockMap :=
  install physical start (headerDecode (physical (SnapshotHome.logHeader start))).2
    (SnapshotHome.restrict physical (SnapshotHome.homeSet coverage start))

/-- The exact source equality predicate does not require a valid header. -/
def Recovers (physical : Blocks) (disk : BlockMap) (coverage : BlockSet) (start : Int) : Prop :=
  disk = recover physical coverage start

/-- Exactly the three source hdr_wf clauses, including superblock exclusion
inside the per-entry clause. No byte-length or padding condition is added. -/
structure HeaderWF (physical : Blocks) (coverage : BlockSet) (start : Int) : Prop where
  count : (headerDecode (physical (SnapshotHome.logHeader start))).1 ≤ SnapshotHome.logBlocks
  distinct : (headerDecode (physical (SnapshotHome.logHeader start))).2.Nodup
  targets : ∀ b, b ∈ (headerDecode (physical (SnapshotHome.logHeader start))).2 →
    b ∈ coverage ∧ b ∉ SnapshotHome.logRegion start ∧ b ≠ 1

/-- Recovery reads absent entries from the original physical view. This is
source fs_rec_view, distinct from dv_of_D's empty-list default. -/
def view (physical : Blocks) (disk : BlockMap) : Blocks :=
  fun b => disk[b]?.getD (physical b)

/-- All decoded destinations remain exceptions, including equal-payload writes. -/
def writeSet (physical : Blocks) (start : Int) : BlockSet :=
  Std.ExtTreeSet.ofList (headerDecode (physical (SnapshotHome.logHeader start))).2

def Full (disk : BlockMap) : Prop :=
  ∀ (b : Int) (bytes : List Byte), disk[b]? = some bytes → bytes.length = 1024

end Xv6.Fs.Recovery
