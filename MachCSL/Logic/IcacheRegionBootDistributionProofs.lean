import MachCSL.Logic.IcacheRegionBootSpec
import MachCSL.Logic.IcacheRegionSlotBootProofs
import MachCSL.Logic.FsInodeRegionBytesProofs

namespace MachCSL.Logic.IcacheRegionBoot
open Iris Iris.Std Iris.BI Xv6.Fs SnapshotConfig
variable {GF : BundledGFunctors}

theorem flat_sixteen (n : Nat) (phi : Nat → IProp GF) :
    bigSepL (fun _ j => phi j) (List.range (16 * n)) ⊣⊢
      bigSepL (fun _ bi => bigSepL (fun _ i => phi (16 * bi + i)) (List.range 16)) (List.range n) := by
  induction n generalizing phi with
  | zero => exact .rfl
  | succ n ih =>
    rw [Nat.mul_succ, show 16 * n + 16 = 16 + 16 * n by omega, List.range_add,
      BigSepL.bigSepL_append.to_eq, BigSepL.bigSepL_map, @List.range_succ_eq_map n,
      BigSepL.bigSepL_cons.to_eq, BigSepL.bigSepL_map]
    apply sep_congr_right
    refine (ih (fun j => phi (16 + j))).trans ?_
    apply BiEntails.of_eq
    apply BigSepL.bigSepL_eq_of_forall_eq
    intro k bi
    apply BigSepL.bigSepL_eq_of_forall_eq
    intro j i
    congr 1
    omega

theorem set_flat (nib : Nat) (phi : Int → IProp GF) :
    bigSepS phi (regionInums nib) ⊣⊢ bigSepL (fun _ (j : Nat) => phi j) (List.range (16 * nib)) := by
  have nodup : ((List.range (16 * nib)).map Int.ofNat).Nodup :=
    List.nodup_range.map Int.ofNat (fun _ _ ne eq => ne (Int.ofNat.inj eq))
  have same (xs : List Int) : _root_.Std.ExtTreeSet.ofList xs = (LawfulSet.ofList xs : BlockSet) := by
    apply _root_.Std.ExtTreeSet.ext_mem
    intro i
    rw [← LawfulSet.mem_ofList]
    simp
  unfold regionInums
  rw [same, (BigSepS.bigSepS_of_list (S := BlockSet) (Φ := phi) nodup).to_eq, BigSepL.bigSepL_map]
  exact .rfl

variable (capacity : Capacity GF) (names : Names) (view : FsView.View GF) (records : GName)

theorem slots_rows (dss : List (List Dinode)) (nib : Nat) :
    slots capacity names view records dss nib ⊣⊢
      bigSepL (fun _ (bi : Nat) => bigSepL (fun _ (i : Nat) =>
        IcacheRegionSlot.ireg_slot capacity names view records (16 * (bi : Int) + (i : Int))
          ((dss[bi]?.getD [])[i]?.getD default)) (List.range 16)) (List.range nib) := by
  unfold slots
  rw [(set_flat nib _).to_eq, (flat_sixteen nib _).to_eq]
  apply BiEntails.of_eq
  apply BigSepL.bigSepL_eq_of_forall_eq
  intro k bi
  apply BigSepL.bigSepL_eq
  intro j i found
  have bound : i < 16 := List.mem_range.mp (List.mem_of_getElem? found)
  have cast : ((16 * bi + i : Nat) : Int) = 16 * (bi : Int) + (i : Int) := by omega
  rw [cast, InodeRegionImage.image_dinode_slot dss bi i bound]

theorem dummy_lookup (nib : Nat) (z : Int) : (dummyRegistry nib)[z]? =
    if z ∈ regionInums nib then some (1, 1) else none := by
  by_cases member : z ∈ regionInums nib
  · rw [if_pos member]
    change get? (FiniteMap.ofSet (M := IcacheEscrowTokens.TokenMap) (1, 1) (regionInums nib)) z = some (1, 1)
    exact LawfulFiniteMap.get?_ofSet_of_mem member
  · rw [if_neg member]
    change get? (FiniteMap.ofSet (M := IcacheEscrowTokens.TokenMap) (1, 1) (regionInums nib)) z = none
    exact LawfulFiniteMap.get?_ofSet_of_not_mem member

theorem dummy_coverage (nib : Nat) (z : Int) (range : 0 ≤ z ∧ z < 16 * (nib : Int)) :
    ((dummyRegistry nib)[z]?).isSome := by
  rw [dummy_lookup, if_pos ((region_inums_spec nib z).mpr range)]
  trivial

theorem dummy_key (nib : Nat) (z : Int) (pair : IcacheEscrowTokens.RegistryValue)
    (found : (dummyRegistry nib)[z]? = some pair) : 0 ≤ z := by
  rw [dummy_lookup] at found
  split at found
  · exact ((region_inums_spec nib z).mp (by assumption)).1
  · contradiction

theorem coveredRegistry_from_map (map : IcacheEscrowTokens.TokenMap IcacheEscrowTokens.RegistryValue)
    (nib : Nat) (coverage : ∀ z : Int, 0 ≤ z ∧ z < 16 * (nib : Int) → (map[z]?).isSome) :
    iprop(IcacheEscrowTokens.reg_auth capacity.escrow names.registry map ⊢ coveredRegistry capacity names nib) := by
  unfold coveredRegistry
  iintro Ha
  iexists map
  iframe Ha
  ipureintro; exact coverage

theorem registry_insert (nib : Nat) :
    iprop(⊢ IcacheEscrowTokens.reg_auth capacity.escrow names.registry ∅ ==∗
      coveredRegistry capacity names nib ∗ registryRows capacity names nib) := by
  letI := capacity.escrow.registry
  have insert : iprop(⊢ IcacheEscrowTokens.reg_auth capacity.escrow names.registry ∅ ==∗
      IcacheEscrowTokens.reg_auth capacity.escrow names.registry (dummyRegistry nib) ∗
      bigSepM (M := IcacheEscrowTokens.TokenMap) (fun z pair =>
        IcacheEscrowTokens.reg_full capacity.escrow names.registry z pair.1 pair.2) (dummyRegistry nib)) := by
    have law := ghost_map_insert_big (H := IcacheEscrowTokens.TokenMap) (GF := GF)
      (γ := names.registry) (dummyRegistry nib) (LawfulPartialMap.disjoint_empty_right _)
    simpa only [LawfulPartialMap.union_empty_right, IcacheEscrowTokens.reg_auth,
      IcacheEscrowTokens.reg_full, IcacheEscrowTokens.reg_elem] using law
  iintro Ha
  imod insert $$ Ha with ⟨Ha, Hrows⟩
  imodintro
  isplitl [Ha]
  · iapply coveredRegistry_from_map capacity names (dummyRegistry nib) nib (dummy_coverage nib) $$ Ha
  · unfold registryRows
    iunfold dummyRegistry at Hrows
    iapply (BigSepM.bigSepM_ofSetWith (M := IcacheEscrowTokens.TokenMap) _ _ _).mp $$ Hrows

/-- Preserve the complete record map, including marker entries, while
regrouping existing byte runs and slots into the exact source body. -/
theorem body_from_rows (start : Int) (blocks : List (List (BitVec 8))) (dss : List (List Dinode))
    (decoded : FsInodeRegion.Decoded blocks dss) :
    iprop(⊢ FsInodeRegion.auth capacity.records records (FsInodeRegion.initialMap dss blocks.length) -∗
      FsInodeRegion.regionRecs view start dss -∗ slots capacity names view records dss blocks.length -∗
      coveredRegistry capacity names blocks.length -∗ body capacity names view records start blocks.length) := by
  unfold FsInodeRegion.regionRecs
  rw [FsInodeRegion.list_rows (fun bi ds => FsInodeRegion.recs view start bi ds) dss, decoded.1,
    (slots_rows capacity names view records dss blocks.length).to_eq]
  iintro Ha Hbytes Hslots Hreg
  unfold body
  iexists FsInodeRegion.initialMap dss blocks.length
  iframe Ha Hreg
  ihave Hrows := (BigSepL.bigSepL_sep_eqv).mpr $$ [$Hbytes $Hslots]
  iapply BigSepL.bigSepL_mono $$ Hrows
  intro k bi found
  have bound : bi < blocks.length := List.mem_range.mp (List.mem_of_getElem? found)
  have bound' : bi < dss.length := by rw [decoded.1]; exact bound
  have wf : InodeBlockWellFormed (dss[bi]?.getD []) := by
    apply decoded.2.1
    simpa only [List.getElem?_eq_getElem bound', Option.getD_some] using List.getElem_mem bound'
  iintro ⟨Hbytes, Hslots⟩
  unfold block
  iexists dss[bi]?.getD []
  iframe Hbytes Hslots
  isplit
  · ipureintro; exact wf
  · ipureintro; exact FsInodeRegion.initial_map_couple dss blocks.length bi bound

end MachCSL.Logic.IcacheRegionBoot
