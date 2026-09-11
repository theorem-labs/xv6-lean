import MachCSL.Logic.FsCfgSnapSpec
import MachCSL.Logic.FsStateLinkProofs
import MachCSL.Logic.FsLinkProofs
import MachCSL.Logic.IcacheInodeCustodyPureProofs
import Xv6.Fs.SnapshotConfigBlockProofs

namespace MachCSL.Logic.FsCfgSnap
open Iris Iris.Std Iris.BI Xv6.Fs SnapshotConfig
variable {GF : BundledGFunctors} (capacity : Capacity GF)

theorem map_as_set (nodes : DurableState.InodeMap) (phi : Int → DurableNode.Node → IProp GF) :
    bigSepM (M := FsState.InodeMap) phi nodes ⊣⊢
      bigSepS (fun i => phi i (nodes[i]?.getD defaultNode))
        (FiniteMap.dom_set (M := FsState.InodeMap) (S := BlockSet) nodes) := by
  have eq : bigSepM (M := FsState.InodeMap) phi nodes =
      bigSepM (M := FsState.InodeMap) (fun i _ => phi i (nodes[i]?.getD defaultNode)) nodes := by
    apply BigSepM.bigSepM_eq
    intro i n found
    change nodes[i]? = some n at found
    simp only [found, Option.getD_some]
  rw [eq]
  exact BigSepM.bigSepM_dom

theorem region_subset state disk (nib : Nat) (bytes : Snapshot.Bytes state disk)
    (weq : (nib : Int) = state.superblock.ninodes / 16 + 1) :
    regionInums nib ⊆ FiniteMap.dom_set (M := FsState.InodeMap) (S := BlockSet) state.inodes := by
  intro i member
  apply LawfulFiniteMap.mem_dom_set.mpr
  exact Option.isSome_iff_exists.mpr ⟨node state i, snap_node_at state disk nib i bytes weq member⟩

theorem links_to_region gl state disk (nib : Nat) (bytes : Snapshot.Bytes state disk)
    (weq : (nib : Int) = state.superblock.ninodes / 16 + 1) :
    FsState.links capacity.crash.links gl state.inodes ⊢
      bigSepS (fun z => FsState.linkNode capacity.crash.links gl z (node state z)) (regionInums nib) := by
  unfold FsState.links
  rw [(map_as_set state.inodes _).to_eq]
  exact BigSepS.bigSepS_subseteq (region_subset state disk nib bytes weq)

theorem kind_ireg (n : DurableNode.Node) (v : FsLink.IType) (kind : LinkFamily.KindOK n v) :
    IcacheInodeCustody.ireg_reg_ok n.typeZ v := by
  cases v <;> simpa [LinkFamily.KindOK, IcacheInodeCustody.ireg_reg_ok, DurableNode.Node.isDir] using kind

theorem multiplicity_ireg (n : DurableNode.Node) :
    LinkFamily.multiplicity n = IcacheInodeCustody.ireg_mult_at (IcacheInodeCustody.ireg_nl n.record) n.record.typeZ := by
  simp [LinkFamily.multiplicity, IcacheInodeCustody.ireg_mult_at, IcacheInodeCustody.ireg_nl, InodeRegionImage.nlink, DurableNode.Node.nlink, DurableNode.Node.isDir, DurableNode.Node.orphan, DurableNode.Node.typeZ]

theorem link_route (view : FsView.View GF) state disk (nib : Nat) ty
    (bytes : Snapshot.Bytes state disk) (weq : (nib : Int) = state.superblock.ninodes / 16 + 1)
    (positive : 0 < nib) :
    iprop(⊢ FsState.links capacity.crash.links view.link state.inodes -∗
      FsLink.tok capacity.crash.links view.link 1 ty -∗
      regionLinks capacity view state nib ∗ regionEntries capacity view state nib) := by
  have root : (1 : Int) ∈ regionInums nib := (region_inums_spec nib 1).mpr (by omega)
  iintro Hlinks Hkeep
  ihave Hlinks := links_to_region capacity view.link state disk nib bytes weq $$ Hlinks
  ihave ⟨Hroot, Hrest⟩ := (BigSepS.bigSepS_delete (Φ := fun z => FsState.linkNode capacity.crash.links view.link z (node state z)) root).mp $$ Hlinks
  unfold regionLinks regionEntries
  rw [← BigSepS.bigSepS_sep.to_eq,
    (BigSepS.bigSepS_delete (Φ := fun z => iprop(
      IcacheInodeCustody.ireg_lnk view capacity.crash.links z (node state z).record ∗
      FsState.entToksX view capacity.crash.links z (node state z))) root).to_eq]
  isplitl [Hroot Hkeep]
  · ihave ⟨⟨%value, %kind, Ha⟩, Hentries⟩ :=
      (FsState.inode_link_iff view capacity.crash.links 1 (node state 1)).mpr $$ Hroot
    ihave %same := FsLink.auth_tok_agree capacity.crash.links view.link 1 _ value ty $$ Ha Hkeep
    rcases same with ⟨rfl, _⟩
    isplitr [Hentries]
    · unfold IcacheInodeCustody.ireg_lnk IcacheInodeCustody.ireg_lnk_at
      iexists ty
      isplit
      · ipureintro; exact kind_ireg _ _ kind
      rw [← multiplicity_ireg]
      iframe Ha
      simp only [IcacheInodeCustody.ireg_keep, ↓reduceIte]
      iexact Hkeep
    · iexact Hentries
  · iapply BigSepS.bigSepS_mono $$ Hrest
    intro z member
    have ne : z ≠ 1 := by
      have outside := (Std.ExtTreeSet.mem_diff_iff.mp member).2
      intro eq; apply outside; simp [eq]
    iintro H
    ihave ⟨⟨%value, %kind, Ha⟩, Hentries⟩ :=
      (FsState.inode_link_iff view capacity.crash.links z (node state z)).mpr $$ H
    isplitr [Hentries]
    · unfold IcacheInodeCustody.ireg_lnk IcacheInodeCustody.ireg_lnk_at
      iexists value
      isplit
      · ipureintro; exact kind_ireg _ _ kind
      rw [← multiplicity_ireg]
      iframe Ha
      simp only [IcacheInodeCustody.ireg_keep, ne, ↓reduceIte]
      iempintro
    · iexact Hentries

theorem top_route (view : FsView.View GF) state disk (nib : Nat)
    (ok : Snapshot.OK state disk) (weq : (nib : Int) = state.superblock.ninodes / 16 + 1) :
    FsTop.allFragments capacity.crash.tops view.top state.inodes ⊢
      liveTops capacity view state nib ∗ regionTopBoot capacity view state nib := by
  have sub : liveSet state nib ⊆ regionInums nib := by
    intro z member
    exact ((elem_of_snap_live_set state nib z).mp member).1
  unfold FsTop.allFragments
  rw [(map_as_set state.inodes _).to_eq]
  change bigSepS (fun z => FsTop.frag capacity.crash.tops view.top z (node state z))
    (FiniteMap.dom_set (M := FsState.InodeMap) (S := BlockSet) state.inodes) ⊢ _
  iintro H
  ihave H := BigSepS.bigSepS_subseteq (Φ := fun z => FsTop.frag capacity.crash.tops view.top z (node state z))
    (region_subset state disk nib ok.1 weq) $$ H
  ihave ⟨Hlive, Hfree⟩ := (BigSepS.bigSepS_split_subset
    (Φ := fun z => FsTop.frag capacity.crash.tops view.top z (node state z)) sub).mp $$ H
  isplitl [Hlive]
  · unfold liveTops FsTop.topFrag FsTop.topFragQ
    iunfold FsTop.frag at Hlive
    iexact Hlive
  · unfold regionTopBoot
    iapply (BigSepS.bigSepS_split_subset (Φ := fun z => topBoot capacity view z (node state z).record) sub).mpr
    isplitr [Hfree]
    · iapply BigSepS.bigSepS_intro (P := emp)
      intro z member
      have live := ((elem_of_snap_live_set state nib z).mp member).2
      unfold topBoot
      simp only [DurableNode.Node.typeZ] at live
      simp only [live, ↓reduceIte]
      exact .rfl
      iempintro
    · iapply BigSepS.bigSepS_mono $$ Hfree
      intro z member
      have ran := (Std.ExtTreeSet.mem_diff_iff.mp member).1
      have outside := (Std.ExtTreeSet.mem_diff_iff.mp member).2
      have zero : (node state z).typeZ = 0 := by
        by_cases zero : (node state z).typeZ = 0
        · exact zero
        · exact False.elim (outside ((elem_of_snap_live_set state nib z).mpr ⟨ran, zero⟩))
      have localNode := ok.2 z (node state z) (snap_node_at state disk nib z ok.1 weq ran)
      have bare := localNode.bareFree zero
      have eq := IcacheInodeCustody.freeNode_of_bare (node state z) bare
      unfold topBoot
      change (node state z).record.typeZ = 0 at zero
      simp only [zero, ↓reduceIte]
      rw [← eq]
      exact .rfl

theorem routeSpec : RouteSpec capacity :=
  ⟨map_as_set, links_to_region capacity, link_route capacity, top_route capacity⟩

end MachCSL.Logic.FsCfgSnap
