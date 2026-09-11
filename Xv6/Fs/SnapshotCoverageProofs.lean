import Xv6.Fs.SnapshotCoverageDefs
import Xv6.Fs.SnapshotHomeProofs

namespace Xv6.Fs.SnapshotCoverage
open DurableState SnapshotHome

theorem snap_names_dom state disk b (bytes : Snapshot.Bytes state disk) (named : Names state b) :
    disk[b]?.isSome := by
  rcases named with metadata | ⟨i, n, found, owns⟩ | ⟨range, free⟩
  · rcases metadata with rfl | rfl | ⟨i, present, rfl⟩
    · rw [bytes.superblock]; trivial
    · rw [bytes.bitmap]; trivial
    · obtain ⟨n, found⟩ := Option.isSome_iff_exists.mp present
      obtain ⟨record, found, _⟩ := bytes.record i n found
      rw [found]; trivial
  · rcases owns with ⟨k, present, rfl⟩ | ⟨nonzero, rfl⟩
    · obtain ⟨data, stored⟩ := Option.isSome_iff_exists.mp present
      rw [bytes.data i n k data found stored]; trivial
    · rw [bytes.indirect i n found nonzero]; trivial
  · exact bytes.pool b range free

theorem snap_names_home state image home b
    (bytes : Snapshot.Bytes state (restrict image home)) (named : Names state b) : b ∈ home :=
  (restrict_domain image home b).mp (snap_names_dom state _ b bytes named)

theorem snap_names_cov state image coverage start b
    (bytes : Snapshot.Bytes state (homeMap image coverage start)) (named : Names state b) :
    b ∈ coverage ∧ b ∉ logRegion start := by
  have member := snap_names_home state image (homeSet coverage start) b bytes named
  exact ⟨homeSet_subset coverage start b member, homeSet_not_log coverage start b member⟩

theorem log_region_range start b (member : b ∈ logRegion start) : start ≤ b ∧ b ≤ start + 30 := by
  have bounds := (logRegion_mem start b).mp member
  omega

theorem log_region_between start b (bounds : start ≤ b ∧ b ≤ start + 30) : b ∈ logRegion start := by
  apply (logRegion_mem start b).mpr
  omega

/-- The rounded inode-region sweep uses inode 16*(b-inodestart), including
records beyond the advertised inode count, exactly as the source does. -/
theorem snap_window_dom state disk b (bytes : Snapshot.Bytes state disk)
    (range : 1 ≤ b ∧ b < dataStart state.superblock) :
    disk[b]?.isSome ∨ b ∈ logRegion state.superblock.logstart := by
  have sb := bytes.superblockOK
  have start := sb.inodestart
  have log := sb.logstart
  have count := sb.nlog
  have bitmap := sb.bmapstart
  have ninodes := sb.ninodes
  unfold dataStart at range
  by_cases one : b = 1
  · subst b
    left; rw [bytes.superblock]; trivial
  by_cases before : b < state.superblock.inodestart
  · right
    apply log_region_between
    omega
  by_cases last : b = state.superblock.bmapstart
  · subst b
    left; rw [bytes.bitmap]; trivial
  have inodeRange : 0 ≤ 16 * (b - state.superblock.inodestart) ∧
      16 * (b - state.superblock.inodestart) < 16 * (state.superblock.ninodes / 16 + 1) := by omega
  obtain ⟨n, found⟩ := Option.isSome_iff_exists.mp (bytes.regionDomain _ inodeRange)
  obtain ⟨record, stored, _⟩ := bytes.record _ n found
  have block : state.superblock.inodestart + 16 * (b - state.superblock.inodestart) / 16 = b := by omega
  rw [block] at stored
  left; rw [stored]; trivial

theorem snap_cov_window state image coverage b
    (bytes : Snapshot.Bytes state (homeMap image coverage state.superblock.logstart))
    (logCovered : ∀ block, block ∈ logRegion state.superblock.logstart → block ∈ coverage)
    (range : 1 ≤ b ∧ b < dataStart state.superblock) : b ∈ coverage := by
  rcases snap_window_dom state _ b bytes range with present | log
  · have home := (restrict_domain image (homeSet coverage state.superblock.logstart) b).mp present
    exact homeSet_subset _ _ _ home
  · exact logCovered b log

theorem snap_cov_below state image coverage b
    (bytes : Snapshot.Bytes state (homeMap image coverage state.superblock.logstart))
    (covered : b ∈ coverage) : 0 ≤ b ∧ b < state.superblock.size := by
  by_cases log : b ∈ logRegion state.superblock.logstart
  · have bounds := log_region_range _ _ log
    have sb := bytes.superblockOK
    have start := sb.inodestart
    have logstart := sb.logstart
    have count := sb.nlog
    have bitmap := sb.bmapstart
    have size := sb.size
    have ninodes := sb.ninodes
    have nblocks := sb.nblocks
    unfold dataStart at size
    omega
  · have home : b ∈ homeSet coverage state.superblock.logstart := by
      rw [homeSet_mem]
      exact ⟨covered, fun range => log ((logRegion_mem _ _).mpr range)⟩
    exact bytes.domainBelow b ((restrict_domain image _ b).mpr home)

end Xv6.Fs.SnapshotCoverage
