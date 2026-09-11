import MachCSL.Logic.FsTopSpec
import MachCSL.Logic.FsViewProofs

namespace MachCSL.Logic.FsTop
open Iris Iris.Std Iris.Algebra Iris.CMRA Iris.BI
variable {GF : BundledGFunctors} (capacity : Capacity GF)

instance authQ_timeless γ dq nodes : Timeless (authQ capacity γ dq nodes) := by
  letI := capacity.top
  unfold authQ
  infer_instance
instance auth_timeless γ nodes : Timeless (auth capacity γ nodes) := by unfold auth; infer_instance
instance fragQ_timeless γ dq i node : Timeless (fragQ capacity γ dq i node) := by
  letI := capacity.top
  unfold fragQ
  infer_instance
instance frag_timeless γ i node : Timeless (frag capacity γ i node) := by unfold frag; infer_instance
instance allFragments_timeless γ nodes : Timeless (allFragments capacity γ nodes) := by
  unfold allFragments
  infer_instance
instance topFragQ_timeless view dq i node : Timeless (topFragQ capacity view dq i node) := by
  unfold topFragQ
  infer_instance
instance topFrag_timeless view i node : Timeless (topFrag capacity view i node) := by
  unfold topFrag
  infer_instance

theorem frag_one γ i node : frag capacity γ i node = fragQ capacity γ (.own 1) i node := rfl
theorem topFrag_one view i node : topFrag capacity view i node = topFragQ capacity view (.own 1) i node := rfl

theorem lookupQ γ dq nodes dq' i node : iprop(⊢ authQ capacity γ dq nodes -∗
    fragQ capacity γ dq' i node -∗ ⌜nodes[i]? = some node⌝) := by
  letI := capacity.top
  exact ghost_map_lookup

theorem lookup γ nodes dq i node : iprop(⊢ auth capacity γ nodes -∗
    fragQ capacity γ dq i node -∗ ⌜nodes[i]? = some node⌝) :=
  lookupQ capacity γ (.own 1) nodes dq i node

theorem auth_agree γ dq1 dq2 left right : iprop(⊢ authQ capacity γ dq1 left -∗
    authQ capacity γ dq2 right -∗ ⌜left = right⌝) := by
  letI := capacity.top
  exact ghost_map_auth_agree (H := TopMap) (GF := GF) γ dq1 dq2 left right

theorem frag_agree γ dq1 dq2 i left right : iprop(⊢ fragQ capacity γ dq1 i left -∗
    fragQ capacity γ dq2 i right -∗ ⌜left = right⌝) := by
  letI := capacity.top
  unfold fragQ
  iintro Hl Hr
  iapply ghost_map_elem_agree (H := TopMap) (GF := GF) γ i dq1 dq2 left right
  iframe Hl Hr

theorem frag_valid γ (dq1 dq2 : DFrac) i left right : iprop(⊢ fragQ capacity γ dq1 i left -∗
    fragQ capacity γ dq2 i right -∗ ⌜✓ (dq1 • dq2)⌝) := by
  letI := capacity.top
  unfold fragQ
  iintro Hl Hr
  have valid := ghost_map_elem_valid_2 (H := TopMap) (GF := GF) γ i dq1 dq2 left right
  have toPure : iprop((✓ (dq1 • dq2) ∧ ⌜left = right⌝) ⊢@{IProp GF} ⌜✓ (dq1 • dq2)⌝) := by
    iintro ⟨%fractionValid, _⟩
    ipureintro
    exact fractionValid
  iapply valid.trans toPure
  iframe Hl Hr

theorem frag_split γ i node (q1 q2 : Qp) :
    fragQ capacity γ (.own (q1 + q2)) i node ⊣⊢
      fragQ capacity γ (.own q1) i node ∗ fragQ capacity γ (.own q2) i node := by
  letI := capacity.top
  exact Fractional.fractional (Φ := fun q : Qp =>
    (ghost_map_elem γ (.own q) i node : IProp GF)) q1 q2

theorem frag_split34 γ i node : frag capacity γ i node ⊣⊢
    fragQ capacity γ (.own Qp.threeQuarters) i node ∗ fragQ capacity γ (.own Qp.quarter) i node := by
  rw [frag_one, ← FsView.threeQuarters_quarter]
  exact frag_split capacity γ i node _ _

theorem topFragQ_split view i node (q1 q2 : Qp) :
    topFragQ capacity view (.own (q1 + q2)) i node ⊣⊢
      topFragQ capacity view (.own q1) i node ∗ topFragQ capacity view (.own q2) i node :=
  frag_split capacity view.top i node q1 q2

theorem topFragQ_agree view dq1 dq2 i left right : iprop(⊢ topFragQ capacity view dq1 i left -∗
    topFragQ capacity view dq2 i right -∗ ⌜left = right⌝) :=
  frag_agree capacity view.top dq1 dq2 i left right

theorem topFrag_gammaQ view dq i node :
    topFrag capacity (FsView.gammaQ view dq) i node = topFrag capacity view i node := rfl

theorem update γ nodes i old new : iprop(⊢ auth capacity γ nodes -∗ frag capacity γ i old ==∗
    auth capacity γ (nodes.insert i new) ∗ frag capacity γ i new) := by
  letI := capacity.top
  have eq : Iris.Std.PartialMap.insert (M := TopMap) nodes i new = nodes.insert i new := by
    apply _root_.Std.ExtTreeMap.ext_getElem?
    intro key
    simp [Iris.Std.insert, _root_.Std.ExtTreeMap.getElem?_alter, _root_.Std.ExtTreeMap.getElem?_insert]
  rw [← eq]
  exact ghost_map_update (H := TopMap) (GF := GF) new

theorem update_frame γ nodes i old new (frame : IProp GF) :
    iprop(⊢ auth capacity γ nodes -∗ (frag capacity γ i old ∗ frame) ==∗
      auth capacity γ (nodes.insert i new) ∗ frag capacity γ i new ∗ frame) := by
  iintro Ha ⟨Hf, HR⟩
  imod update capacity γ nodes i old new $$ Ha Hf with ⟨Ha, Hf⟩
  imodintro
  iframe Ha Hf HR

theorem update_other (nodes : Xv6.Fs.DurableState.InodeMap) (i : Int) (new : Node)
    (j : Int) (different : i ≠ j) :
    (nodes.insert i new)[j]? = nodes[j]? := by
  simp only [_root_.Std.ExtTreeMap.getElem?_insert, _root_.Std.compare_eq_eq_iff_eq, if_neg different]

theorem insert γ nodes i node (fresh : nodes[i]? = none) :
    iprop(⊢ auth capacity γ nodes ==∗ auth capacity γ (nodes.insert i node) ∗ frag capacity γ i node) := by
  letI := capacity.top
  have eq : Iris.Std.PartialMap.insert (M := TopMap) nodes i node = nodes.insert i node := by
    apply _root_.Std.ExtTreeMap.ext_getElem?
    intro key
    simp [Iris.Std.insert, _root_.Std.ExtTreeMap.getElem?_alter, _root_.Std.ExtTreeMap.getElem?_insert]
  rw [← eq]
  exact ghost_map_insert (H := TopMap) (GF := GF) i node fresh

theorem allocate (nodes : Xv6.Fs.DurableState.InodeMap) :
    iprop(⊢ |==> ∃ γ, auth capacity γ nodes ∗ allFragments capacity γ nodes) := by
  letI := capacity.top
  exact ghost_map_alloc (H := TopMap) (GF := GF) nodes

theorem allFragments_lookup γ nodes i node (found : nodes[i]? = some node) :
    allFragments capacity γ nodes ⊢ frag capacity γ i node := by
  unfold allFragments
  exact BigSepM.bigSepM_lookup (M := TopMap) found

theorem topFrag_full_excl γ i left right :
    iprop(⊢ frag capacity γ i left -∗ frag capacity γ i right -∗ False) := by
  unfold frag
  iintro Hl Hr
  ihave %valid := frag_valid capacity γ (.own 1) (.own 1) i left right $$ Hl Hr
  ipureintro
  exact FsView.dfrac_full_invalid _ valid

theorem actual : FsTopSpec capacity where
  lookup := lookup capacity
  agree := frag_agree capacity
  split := frag_split capacity
  update := update capacity
  allocate := allocate capacity

end MachCSL.Logic.FsTop
