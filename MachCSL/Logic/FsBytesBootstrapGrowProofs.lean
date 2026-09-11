import MachCSL.Logic.FsBytesBootstrapPureProofs
import MachCSL.Logic.FsDurBytesLedgerProofs
import MachCSL.Logic.DiskProofs

namespace MachCSL.Logic.FsBytesBootstrap
open Iris Iris.Std Iris.BI
open FsDurBytes FsBytesInvariant
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem blockRuns_flatten (g : GName) (cache : BlockMap) (full : BlocksFull cache) :
    imageBytesFull capacity.bytes g (flatten cache) ⊣⊢ blockRuns capacity g cache := by
  exact flatten_blocks (FsView.snapGamma capacity.bytes g 1 1) cache full

theorem byte_map_grow g (cache : BlockMap) (oldBytes : ByteMap) (oldHome : BlockSet)
    (full : BlocksFull cache)
    (fresh : ∀ b, b ∈ FiniteMap.dom_set (S := BlockSet) cache → b ∉ oldHome)
    (domain : bytes_dom oldBytes oldHome) (frame : IProp GF) :
    iprop(⊢ Disk.mapAuth capacity.bytes g oldBytes -∗ frame ==∗ ∃ bytes : ByteMap,
      ⌜bytes_dom bytes (oldHome ∪ FiniteMap.dom_set (S := BlockSet) cache)⌝ ∗
      ⌜bytes_tie bytes cache⌝ ∗ Disk.mapAuth capacity.bytes g bytes ∗
      blockRuns capacity g cache ∗ frame) := by
  letI := capacity.bytes.image
  iintro Ha Hframe
  iunfold Disk.mapAuth at Ha
  imod ghost_map_insert_big (flatten cache) (flatten_fresh cache oldBytes oldHome full fresh domain) $$ Ha with ⟨Ha, Hb⟩
  imodintro
  iexists (PartialMap.union (flatten cache) oldBytes)
  unfold Disk.mapAuth
  iframe Ha Hframe
  isplit
  · ipureintro
    exact union_domain _ _ _ _ (flatten_domain cache full) domain
  · isplit
    · ipureintro
      exact union_tie _ _ _ (flatten_tie cache full)
    · iapply (blockRuns_flatten capacity g cache full).mp
      unfold imageBytesFull Disk.imageByte
      iexact Hb

/-- Exact payload-polymorphic source fs_split_filter. -/
theorem fs_split_filter {V : Type} (map : FsBlockGhost.BlockMap V) (home : BlockSet)
    (Φ : Int → V → IProp GF) :
    bigSepM Φ map ⊢
      bigSepM Φ (PartialMap.filter (fun b (_ : V) => decide (b ∈ home)) map) ∗
      bigSepM Φ (PartialMap.filter (fun b (_ : V) => decide (b ∉ home)) map) := by
  obtain ⟨same, disjoint⟩ := filter_partition map home
  have law := BigSepM.bigSepM_union (M := FsBlockGhost.BlockMap) (Φ := Φ) disjoint
  change bigSepM Φ (PartialMap.union _ _) ⊣⊢ _ at law
  rw [same] at law
  exact law.mp

theorem filter_split (cache : BlockMap) (home : BlockSet) (Φ : Int → List Byte → IProp GF) :
    bigSepM Φ cache ⊣⊢ bigSepM Φ (homeMap cache home) ∗ bigSepM Φ (outsideMap cache home) := by
  have law := BigSepM.bigSepM_union (M := FsBlockGhost.BlockMap) (Φ := Φ) (filter_disjoint cache home)
  change bigSepM Φ (PartialMap.union (homeMap cache home) (outsideMap cache home)) ⊣⊢ _ at law
  rw [filter_union cache home] at law
  exact law

theorem valueMap_runs (g : GName) (cache : BlockMap) values :
    blockRuns capacity g (valueMap cache values) ⊣⊢ committedRuns capacity g cache values := by
  have pointwise : bigSepM (M := FsBlockGhost.BlockMap)
      (fun b bs => FsBlocks.block capacity.bytes g b bs) (valueMap cache values) ⊣⊢
      bigSepM (M := FsBlockGhost.BlockMap)
        (fun b _ => FsBlocks.block capacity.bytes g b (values b)) (valueMap cache values) := by
    apply BiEntails.of_eq
    apply BigSepM.bigSepM_eq
    intro b bs found
    rw [valueMap_lookup] at found
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp found
    rfl
  unfold blockRuns committedRuns
  rw [pointwise.to_eq,
    (BigSepM.bigSepM_dom (S := BlockSet)).to_eq,
    valueMap_domain,
    ← (BigSepM.bigSepM_dom (S := BlockSet)).to_eq]
  exact .rfl

end MachCSL.Logic.FsBytesBootstrap
