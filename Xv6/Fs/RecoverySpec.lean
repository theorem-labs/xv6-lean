import Xv6.Fs.RecoveryDefs

namespace Xv6.Fs.Recovery
open MachCSL.Memory

/-- Total decoder laws from LogDefs; no HeaderWF premise. -/
structure CodecSpec : Prop where
  nonnegative : ∀ bytes, 0 ≤ headerN bytes
  word_zero : ∀ bytes, headerWord bytes 0 = headerN bytes
  count : ∀ bytes, ((headerDecode bytes).1 : Int) = headerN bytes
  length : ∀ bytes, (headerDecode bytes).2.length = (headerDecode bytes).1
  zero : ∀ bytes, headerN bytes = 0 → headerDecode bytes = (0, [])
  clean_wf : ∀ physical coverage start,
    headerN (physical (SnapshotHome.logHeader start)) = 0 → HeaderWF physical coverage start

/-- Source ordered-install algebra. The hit and idempotence laws retain the
source duplicate-free hypothesis; misses and fullness do not require it. -/
structure InstallSpec : Prop where
  step_some : ∀ (physical : Blocks) (start : Int) (writes : List Int) (i : Nat) (disk : BlockMap) (b : Int), writes[i]? = some b →
    installStep physical start writes i disk = disk.insert b (physical (SnapshotHome.logSlot start i))
  step_none : ∀ (physical : Blocks) (start : Int) (writes : List Int) (i : Nat) (disk : BlockMap), writes[i]? = none →
    installStep physical start writes i disk = disk
  miss : ∀ (physical : Blocks) (start : Int) (writes : List Int) (disk : BlockMap) (b : Int), b ∉ writes →
    (install physical start writes disk)[b]? = disk[b]?
  hit : ∀ (physical : Blocks) (start : Int) (writes : List Int) (disk : BlockMap) (i : Nat) (b : Int), writes.Nodup → writes[i]? = some b →
    (install physical start writes disk)[b]? = some (physical (SnapshotHome.logSlot start i))
  full : ∀ (physical : Blocks) (start : Int) (writes : List Int) (disk : BlockMap),
    (∀ b, (physical b).length = 1024) → Full disk → Full (install physical start writes disk)
  idempotent : ∀ (physical : Blocks) (start : Int) (writes : List Int) (disk : BlockMap), writes.Nodup →
    (∀ i b, writes[i]? = some b → disk[b]? = some (physical (SnapshotHome.logSlot start i))) →
    install physical start writes disk = disk

/-- Exact FsCrash recovery and mint facts, with every required header and
home premise retained. No resource allocation or snapshot validity is assumed. -/
structure Spec : Prop where
  total : ∀ physical coverage start, ∃ disk, Recovers physical disk coverage start
  deterministic : ∀ physical left right coverage start,
    Recovers physical left coverage start → Recovers physical right coverage start → left = right
  clean : ∀ (physical : Blocks) (disk : BlockMap) (coverage : BlockSet) (start : Int),
    headerN (physical (SnapshotHome.logHeader start)) = 0 →
    Recovers physical disk coverage start →
    disk = SnapshotHome.restrict physical (SnapshotHome.homeSet coverage start)
  full : ∀ (physical : Blocks) (disk : BlockMap) (coverage : BlockSet) (start : Int),
    (∀ b, (physical b).length = 1024) → Recovers physical disk coverage start → Full disk
  disk_full : ∀ (physical : Disk) (disk : BlockMap) (coverage : BlockSet) (start : Int),
    Recovers (blocks physical) disk coverage start → Full disk
  writeSet_mem : ∀ physical start b, b ∈ writeSet physical start ↔
    b ∈ (headerDecode (physical (SnapshotHome.logHeader start))).2
  writeSet_home : ∀ physical coverage start, HeaderWF physical coverage start →
    ∀ b, b ∈ writeSet physical start → b ∈ SnapshotHome.homeSet coverage start
  writeSet_superblock : ∀ physical coverage start, HeaderWF physical coverage start →
    1 ∉ writeSet physical start
  domain : ∀ (physical : Blocks) (disk : BlockMap) (coverage : BlockSet) (start : Int),
    Recovers physical disk coverage start → HeaderWF physical coverage start →
    ∀ b, disk[b]?.isSome ↔ b ∈ SnapshotHome.homeSet coverage start
  restrict_view : ∀ (physical : Blocks) (disk : BlockMap) (coverage : BlockSet) (start : Int),
    Recovers physical disk coverage start → HeaderWF physical coverage start →
    SnapshotHome.restrict (view physical disk) (SnapshotHome.homeSet coverage start) = disk
  view_full : ∀ (physical : Blocks) (disk : BlockMap),
    (∀ b, (physical b).length = 1024) → Full disk → ∀ b, (view physical disk b).length = 1024
  untouched : ∀ physical disk coverage start b,
    Recovers physical disk coverage start → b ∈ SnapshotHome.homeSet coverage start →
    b ∉ (headerDecode (physical (SnapshotHome.logHeader start))).2 →
    disk[b]? = some (physical b)
  raw : ∀ physical disk coverage start b,
    Recovers physical disk coverage start → HeaderWF physical coverage start →
    b ∈ SnapshotHome.homeSet coverage start → b ∉ writeSet physical start →
    view physical disk b = physical b
  slot : ∀ physical disk coverage start i b,
    Recovers physical disk coverage start → HeaderWF physical coverage start →
    (headerDecode (physical (SnapshotHome.logHeader start))).2[i]? = some b →
    view physical disk b = physical (SnapshotHome.logSlot start i)
  superblock : ∀ (physical : Blocks) (disk : BlockMap) (coverage : BlockSet) (start : Int),
    Recovers physical disk coverage start → HeaderWF physical coverage start →
    1 ∈ SnapshotHome.homeSet coverage start → disk[(1 : Int)]? = some (physical 1)

end Xv6.Fs.Recovery
