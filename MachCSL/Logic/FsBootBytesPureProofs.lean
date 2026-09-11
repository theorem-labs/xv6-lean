import MachCSL.Logic.FsBootBytesSpec
import MachCSL.Logic.FsBytesBootstrapPureProofs
import Xv6.Fs.SnapshotHomeProofs

set_option maxRecDepth 2048

namespace MachCSL.Logic.FsBootBytes
open Iris Iris.Std Iris.BI MachCSL.Memory

theorem rawMap_lookup disk covered b bytes :
    (rawMap disk covered)[b]? = some bytes ↔ b ∈ covered ∧ bytes = Xv6.Fs.blocks disk b :=
  Xv6.Fs.SnapshotHome.restrict_lookup_some _ _ _ _

theorem rawMap_domain disk covered :
    FiniteMap.dom_set (M := Disk.ImageMap) (S := BlockSet) (rawMap disk covered) = covered := by
  apply LawfulSet.ext
  intro b
  rw [LawfulFiniteMap.mem_dom_set]
  exact Xv6.Fs.SnapshotHome.restrict_domain _ _ _

theorem rawMap_full disk covered : FsDurBytes.BlocksFull (rawMap disk covered) := by
  intro b bytes found
  obtain ⟨_, rfl⟩ := (rawMap_lookup _ _ _ _).mp found
  exact Xv6.Fs.blocks_length _ _

theorem rawMap_filter_in disk covered home (sub : home ⊆ covered) :
    FsBytesBootstrap.homeMap (rawMap disk covered) home = rawMap disk home := by
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro b
  change get? (FsBytesBootstrap.homeMap (rawMap disk covered) home) b = _
  rw [FsBytesBootstrap.homeMap_lookup]
  change (if b ∈ home then (rawMap disk covered)[b]? else none) = _
  simp only [rawMap, Xv6.Fs.SnapshotHome.restrict_lookup]
  by_cases hin : b ∈ home
  · simp [hin, sub b hin]
  · simp [hin]

theorem rawMap_filter_out disk covered home :
    FsBytesBootstrap.outsideMap (rawMap disk covered) home = rawMap disk (covered \ home) := by
  apply _root_.Std.ExtTreeMap.ext_getElem?
  intro b
  change get? (FsBytesBootstrap.outsideMap (rawMap disk covered) home) b = _
  rw [FsBytesBootstrap.outsideMap_lookup]
  change (if b ∈ home then none else (rawMap disk covered)[b]?) = _
  simp only [rawMap, Xv6.Fs.SnapshotHome.restrict_lookup, _root_.Std.ExtTreeSet.mem_diff_iff]
  by_cases hin : b ∈ home <;> simp [hin]

theorem covered_bytes_submap disk length covered (bound : Xv6.Fs.CovIn covered length) :
    PartialMap.submap (M := Disk.ImageMap) (FsDurBytes.flatten (rawMap disk covered))
      (suppliedMap disk length) := by
  intro a v found
  change (FsDurBytes.flatten (rawMap disk covered))[a]? = some v at found
  obtain ⟨b, bytes, k, hb, hk, addr⟩ := (FsDurBytes.flatten_lookup _ _ _
    (FsDurBytes.dbytesOK_full _ (rawMap_full disk covered))).mp found
  obtain ⟨coveredB, rfl⟩ := (rawMap_lookup _ _ _ _).mp hb
  have kbound : k < 1024 := by
    have h := (List.getElem?_eq_some_iff.mp hk).1
    simpa only [Xv6.Fs.blocks_length] using h
  have avalue : disk a = v := by
    have h : Xv6.Fs.byteAt (Xv6.Fs.blocks disk b) k = v := by
      simp [Xv6.Fs.byteAt, hk]
    rw [Xv6.Fs.blocks_byte _ _ _ kbound] at h
    simpa only [addr] using h
  obtain ⟨positive, endBound⟩ := bound b coveredB
  have arange : 0 ≤ a ∧ a < length := by omega
  change (suppliedMap disk length)[a]? = some v
  apply (FsDurBytes.byteRun_lookup _ _ _ _).mpr
  refine ⟨a.toNat, ?_, by omega⟩
  have keybound : a.toNat < length := by omega
  simp only [Devices.Virtio.disk_read, List.getElem?_map,
    List.getElem?_range keybound, Option.map_some, Int.zero_add,
    Int.toNat_of_nonneg arange.1, avalue]

theorem pureSpec : PureSpec :=
  ⟨rawMap_lookup, rawMap_domain, rawMap_full, rawMap_filter_in, rawMap_filter_out, covered_bytes_submap⟩

end MachCSL.Logic.FsBootBytes
