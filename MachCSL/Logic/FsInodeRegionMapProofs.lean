import MachCSL.Logic.FsInodeRegionDefs
import Xv6.Fs.InodeRegionImageProofs

namespace MachCSL.Logic.FsInodeRegion
open Iris Iris.Std Xv6.Fs SnapshotConfig

theorem markKey_injective : Function.Injective markKey := by
  intro i j same
  unfold markKey at same
  omega

theorem mark_inums_spec nib i : i ∈ markInums nib ↔ ∃ j, j ∈ regionInums nib ∧ i = markKey j := by
  simp only [markInums, _root_.Std.ExtTreeSet.mem_ofList, List.contains_iff_mem, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, bound, rfl⟩
    exact ⟨k, (region_inums_spec nib k).mpr (by omega), rfl⟩
  · rintro ⟨j, member, rfl⟩
    have bounds := (region_inums_spec nib j).mp member
    exact ⟨j.toNat, by omega, by congr 1; change (j.toNat : Int) = j; omega⟩

theorem mark_negative nib i (member : i ∈ markInums nib) : i < 0 := by
  obtain ⟨j, hj, rfl⟩ := (mark_inums_spec nib i).mp member
  have bounds := (region_inums_spec nib j).mp hj
  unfold markKey
  omega

theorem ofSetWith_lookup (f : Int → Dinode) (set : BlockSet) i record :
    (FiniteMap.ofSetWith (M := RecordMap) f set)[i]? = some record ↔ i ∈ set ∧ record = f i := by
  change get? (M := RecordMap) (FiniteMap.ofSetWith f set) i = some record ↔ _
  rw [← LawfulFiniteMap.toList_get, (LawfulFiniteMap.toList_ofSetWith (M := RecordMap)).mem_iff]
  simp only [List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨j, member, rfl, rfl⟩
    exact ⟨FiniteSet.mem_toList.mp member, rfl⟩
  · rintro ⟨member, rfl⟩
    exact ⟨i, FiniteSet.mem_toList.mpr member, rfl, rfl⟩

theorem initial_records_lookup records nib i record :
    (initialRecords records nib)[i]? = some record ↔ i ∈ regionInums nib ∧ record = InodeRegionImage.imageDinode records i :=
  ofSetWith_lookup _ _ _ _

theorem initial_markers_lookup nib i record :
    (initialMarkers nib)[i]? = some record ↔ i ∈ markInums nib ∧ record = markRecord :=
  ofSetWith_lookup _ _ _ _

theorem initial_maps_disjoint records nib : PartialMap.disjoint (initialRecords records nib) (initialMarkers nib) := by
  intro i ⟨left, right⟩
  obtain ⟨dn, hd⟩ := Option.isSome_iff_exists.mp left
  obtain ⟨mark, hm⟩ := Option.isSome_iff_exists.mp right
  have nonneg := ((region_inums_spec nib i).mp ((initial_records_lookup records nib i dn).mp hd).1).1
  have neg := mark_negative nib i ((initial_markers_lookup nib i mark).mp hm).1
  omega

theorem inum_cast (nib : Nat) i (bound : 16 * (nib : Int) ≤ 2 ^ 32) (member : i ∈ regionInums nib) :
    ((BitVec.ofInt 32 i).toNat : Int) = i := by
  have bounds := (region_inums_spec nib i).mp member
  simp only [BitVec.toNat_ofInt]
  rw [Int.emod_eq_of_lt bounds.1 (by omega)]
  omega

theorem initial_couple records nib bi (bound : bi < nib) :
    couple (initialRecords records nib) bi (records[bi]?.getD []) := by
  intro i hi
  apply (initial_records_lookup records nib _ _).mpr
  refine ⟨(region_inums_spec nib _).mpr (by omega), ?_⟩
  exact (InodeRegionImage.image_dinode_slot records bi i hi).symm

theorem initial_records_domain records nib i :
    (initialRecords records nib)[i]?.isSome ↔ i ∈ regionInums nib := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨dn, found⟩; exact ((initial_records_lookup records nib i dn).mp found).1
  · intro member
    exact ⟨_, (initial_records_lookup records nib i _).mpr ⟨member, rfl⟩⟩

theorem initial_markers_domain nib i :
    (initialMarkers nib)[i]?.isSome ↔ i ∈ markInums nib := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨dn, found⟩; exact ((initial_markers_lookup nib i dn).mp found).1
  · intro member
    exact ⟨_, (initial_markers_lookup nib i _).mpr ⟨member, rfl⟩⟩

theorem initial_map_lookup records nib (i : Int) : (initialMap records nib)[i]? =
    (initialRecords records nib)[i]?.orElse (fun _ => (initialMarkers nib)[i]?) :=
  LawfulPartialMap.get?_union (M := RecordMap)

theorem initial_map_record records nib i (member : i ∈ regionInums nib) :
    (initialMap records nib)[i]? = some (InodeRegionImage.imageDinode records i) := by
  rw [initial_map_lookup]
  have found := (initial_records_lookup records nib i _).mpr ⟨member, rfl⟩
  rw [found]
  rfl

theorem initial_map_marker records nib i (member : i ∈ regionInums nib) :
    (initialMap records nib)[markKey i]? = some markRecord := by
  have marked : markKey i ∈ markInums nib := (mark_inums_spec nib _).mpr ⟨i, member, rfl⟩
  have negative := mark_negative nib _ marked
  have absent : (initialRecords records nib)[markKey i]? = none := by
    apply Option.not_isSome_iff_eq_none.mp
    intro present
    have bounds := (region_inums_spec nib _).mp ((initial_records_domain records nib _).mp present)
    omega
  have found := (initial_markers_lookup nib _ _).mpr ⟨marked, rfl⟩
  rw [initial_map_lookup]
  rw [absent, found]
  rfl

theorem initial_map_couple records nib bi (bound : bi < nib) :
    couple (initialMap records nib) bi (records[bi]?.getD []) := by
  intro i hi
  rw [initial_map_record records nib _ ((region_inums_spec nib _).mpr (by omega))]
  congr 1
  exact InodeRegionImage.image_dinode_slot records bi i hi

end MachCSL.Logic.FsInodeRegion
