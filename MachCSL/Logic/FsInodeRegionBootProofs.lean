import MachCSL.Logic.FsInodeRegionProofs
import MachCSL.Logic.FsInodeRegionMapProofs
import Xv6.Fs.InodeRegionImageProofs

namespace MachCSL.Logic.FsInodeRegion
open Iris Iris.Std Iris.BI Xv6.Fs SnapshotConfig
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem initial_fragments g records nib : allFragments capacity g (initialMap records nib) ⊣⊢
    allFragments capacity g (initialRecords records nib) ∗ allFragments capacity g (initialMarkers nib) := by
  unfold allFragments initialMap
  exact BigSepM.bigSepM_union (initial_maps_disjoint records nib)

theorem record_fragments g records nib : allFragments capacity g (initialRecords records nib) ⊣⊢
    bigSepS (fun i => frag capacity g i (InodeRegionImage.imageDinode records i)) (regionInums nib) := by
  unfold allFragments initialRecords
  exact BigSepM.bigSepM_ofSetWith _ _ _

theorem marker_fragments g nib : allFragments capacity g (initialMarkers nib) ⊣⊢
    bigSepS (fun i => frag capacity g (markKey i) markRecord) (regionInums nib) := by
  unfold allFragments initialMarkers
  rw [(BigSepM.bigSepM_ofSetWith (M := RecordMap) _ _ _).to_eq]
  have hn : ((List.range (16 * nib)).map Int.ofNat).Nodup :=
    (List.nodup_range).map Int.ofNat (fun _ _ ne eq => ne (Int.ofNat.inj eq))
  have hm : ((List.range (16 * nib)).map (fun i => markKey (Int.ofNat i))).Nodup := by
    simpa only [List.map_map, Function.comp_def] using List.nodup_map_of_injective markKey_injective hn
  have sets (xs : List Int) : _root_.Std.ExtTreeSet.ofList xs = (LawfulSet.ofList xs : BlockSet) := by
    apply _root_.Std.ExtTreeSet.ext_mem
    intro i
    rw [← LawfulSet.mem_ofList]
    simp
  unfold markInums regionInums
  rw [sets, sets]
  rw [(BigSepS.bigSepS_of_list (S := BlockSet) (Φ := fun i => frag capacity g i markRecord) hm).to_eq,
    (BigSepS.bigSepS_of_list (S := BlockSet) (Φ := fun i => frag capacity g (markKey i) markRecord) hn).to_eq]
  simp only [BigSepL.bigSepL_map]
  exact .rfl

theorem boot_cells g records (nib : Nat) (bound : 16 * (nib : Int) ≤ 2 ^ 32) :
    allFragments capacity g (initialMap records nib) ⊢ bootCells capacity g records nib := by
  rw [(initial_fragments capacity g records nib).to_eq,
    (record_fragments capacity g records nib).to_eq, (marker_fragments capacity g nib).to_eq,
    ← BigSepS.bigSepS_sep.to_eq]
  unfold bootCells
  apply BigSepS.bigSepS_mono
  intro i member
  unfold dinodeAt
  rw [inum_cast nib i bound member]
  iintro ⟨Hr, Hm⟩
  isplitl [Hr]
  · iexact Hr
  · unfold imark
    iexists markRecord
    iexact Hm

theorem boot_allocate records (nib : Nat) (bound : 16 * (nib : Int) ≤ 2 ^ 32) (frame : IProp GF) :
    iprop(frame ⊢ |==> ∃ g, auth capacity g (initialMap records nib) ∗ bootCells capacity g records nib ∗ frame) := by
  iintro HR
  imod allocate capacity (initialMap records nib) with ⟨%g, Ha, Hf⟩
  ihave Hcells := boot_cells capacity g records nib bound $$ Hf
  imodintro
  iexists g
  iframe Ha Hcells HR

theorem actual : Spec capacity where
  lookup := lookup capacity
  markerExclusive := imark_exclusive capacity
  allocate := allocate capacity
  boot := boot_allocate capacity

end MachCSL.Logic.FsInodeRegion
