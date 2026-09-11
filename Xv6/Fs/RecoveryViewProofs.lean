import Xv6.Fs.RecoveryProofs

namespace Xv6.Fs.Recovery

theorem recovery_total physical coverage start : ∃ disk, Recovers physical disk coverage start :=
  ⟨recover physical coverage start, rfl⟩

theorem recovery_deterministic physical left right coverage start
    (hl : Recovers physical left coverage start) (hr : Recovers physical right coverage start) :
    left = right := hl.trans hr.symm

theorem recovery_clean physical disk coverage start
    (zero : headerN (physical (SnapshotHome.logHeader start)) = 0)
    (recovery : Recovers physical disk coverage start) :
    disk = SnapshotHome.restrict physical (SnapshotHome.homeSet coverage start) := by
  rw [recovery]
  simp [recover, headerDecode_zero _ zero, install]

theorem recovery_full (physical : Blocks) disk coverage start
    (allFull : ∀ b, (physical b).length = 1024) (recovery : Recovers physical disk coverage start) :
    Full disk := by
  rw [recovery]
  apply install_full _ _ _ _ allFull
  intro b bytes found
  obtain ⟨_, same⟩ := SnapshotHome.restrict_lookup_some _ _ _ _ |>.mp found
  rw [same]
  exact allFull b

theorem recovery_disk_full physical disk coverage start
    (recovery : Recovers (blocks physical) disk coverage start) : Full disk :=
  recovery_full _ _ _ _ (blocks_length physical) recovery

theorem writeSet_mem physical start b : b ∈ writeSet physical start ↔
    b ∈ (headerDecode (physical (SnapshotHome.logHeader start))).2 := by
  simp [writeSet, Std.ExtTreeSet.mem_ofList]

theorem writeSet_home physical coverage start (wf : HeaderWF physical coverage start)
    b (member : b ∈ writeSet physical start) : b ∈ SnapshotHome.homeSet coverage start := by
  obtain ⟨covered, outside, _⟩ := wf.targets b ((writeSet_mem _ _ _).mp member)
  exact Std.ExtTreeSet.mem_diff_iff.mpr ⟨covered, outside⟩

theorem writeSet_superblock physical coverage start (wf : HeaderWF physical coverage start) :
    1 ∉ writeSet physical start := by
  intro member
  exact (wf.targets 1 ((writeSet_mem _ _ _).mp member)).2.2 rfl

theorem recovery_untouched physical disk coverage start b
    (recovery : Recovers physical disk coverage start)
    (home : b ∈ SnapshotHome.homeSet coverage start)
    (outside : b ∉ (headerDecode (physical (SnapshotHome.logHeader start))).2) :
    disk[b]? = some (physical b) := by
  rw [recovery, recover, install_miss _ _ _ _ _ outside]
  exact (SnapshotHome.restrict_lookup_some _ _ _ _).mpr ⟨home, rfl⟩

theorem recovery_domain physical disk coverage start
    (recovery : Recovers physical disk coverage start) (wf : HeaderWF physical coverage start) b :
    disk[b]?.isSome ↔ b ∈ SnapshotHome.homeSet coverage start := by
  by_cases member : b ∈ (headerDecode (physical (SnapshotHome.logHeader start))).2
  · obtain ⟨i, found⟩ := List.mem_iff_getElem?.mp member
    have home : b ∈ SnapshotHome.homeSet coverage start :=
      writeSet_home _ _ _ wf b ((writeSet_mem _ _ _).mpr member)
    rw [recovery, recover, install_hit _ _ _ _ _ _ wf.distinct found]
    simp [home]
  · rw [recovery, recover, install_miss _ _ _ _ _ member]
    exact SnapshotHome.restrict_domain _ _ b

theorem recovery_restrict_view physical disk coverage start
    (recovery : Recovers physical disk coverage start) (wf : HeaderWF physical coverage start) :
    SnapshotHome.restrict (view physical disk) (SnapshotHome.homeSet coverage start) = disk := by
  apply Std.ExtTreeMap.ext_getElem?
  intro b
  rw [SnapshotHome.restrict_lookup]
  by_cases home : b ∈ SnapshotHome.homeSet coverage start
  · rw [if_pos home]
    have present := (recovery_domain _ _ _ _ recovery wf b).mpr home
    cases found : disk[b]? with
    | none => simp [found] at present
    | some bytes => simp [view, found]
  · rw [if_neg home]
    cases found : disk[b]? with
    | none => rfl
    | some bytes =>
      exfalso
      exact home ((recovery_domain _ _ _ _ recovery wf b).mp (by simp [found]))

theorem view_full (physical : Blocks) disk (allFull : ∀ b, (physical b).length = 1024)
    (full : Full disk) b : (view physical disk b).length = 1024 := by
  cases found : disk[b]? with
  | none => simpa [view, found] using allFull b
  | some bytes => simpa [view, found] using full b bytes found

theorem recovery_raw physical disk coverage start b
    (recovery : Recovers physical disk coverage start) (_wf : HeaderWF physical coverage start)
    (home : b ∈ SnapshotHome.homeSet coverage start) (outside : b ∉ writeSet physical start) :
    view physical disk b = physical b := by
  have missing : b ∉ (headerDecode (physical (SnapshotHome.logHeader start))).2 :=
    fun member => outside ((writeSet_mem _ _ _).mpr member)
  simp [view, recovery_untouched _ _ _ _ _ recovery home missing]

theorem recovery_slot physical disk coverage start i b
    (recovery : Recovers physical disk coverage start) (wf : HeaderWF physical coverage start)
    (found : (headerDecode (physical (SnapshotHome.logHeader start))).2[i]? = some b) :
    view physical disk b = physical (SnapshotHome.logSlot start i) := by
  have hit : disk[b]? = some (physical (SnapshotHome.logSlot start i)) := by
    rw [recovery, recover, install_hit _ _ _ _ _ _ wf.distinct found]
  simp [view, hit]

theorem recovery_superblock physical disk coverage start
    (recovery : Recovers physical disk coverage start) (wf : HeaderWF physical coverage start)
    (home : 1 ∈ SnapshotHome.homeSet coverage start) : disk[(1 : Int)]? = some (physical 1) := by
  apply recovery_untouched _ _ _ _ _ recovery home
  intro member
  exact (wf.targets 1 member).2.2 rfl

theorem actual : Spec :=
  ⟨recovery_total, recovery_deterministic, recovery_clean, recovery_full, recovery_disk_full,
    writeSet_mem, writeSet_home, writeSet_superblock, recovery_domain, recovery_restrict_view,
    view_full, recovery_untouched, recovery_raw, recovery_slot, recovery_superblock⟩

end Xv6.Fs.Recovery
