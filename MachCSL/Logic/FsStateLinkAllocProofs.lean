import MachCSL.Logic.FsStateLinkGatherProofs
import MachCSL.Logic.FsTopProofs
import Xv6.Fs.LinkSupplyProofs

/-! Fresh source boot allocation from explicit native-camera validity.
These lemmas allocate names in the existing GF; they do not allocate an Iris
world or establish durable byte ownership or a reboot transfer. -/
namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Iris.CMRA Iris.Algebra Xv6.Fs FsView
variable {GF : BundledGFunctors} (capacity : FsLink.Capacity GF)

theorem links_scatter γ nodes f (ok : LinkFamily.ElemOK nodes f) :
    iOwn (E := capacity.link) γ (LinkFamily.elem nodes f) ⊢ links capacity γ nodes := by
  refine (own_map_scatter (M := FsLink.FamilyMap) capacity γ
    (fun i n => LinkFamily.nodeElem i n (LinkFamily.choiceValue f i) (LinkFamily.choiceTypes f i)) nodes).trans ?_
  unfold links linkNode
  apply BigSepM.bigSepM_mono
  intro i n found
  iintro H
  iexists LinkFamily.choiceMarkers f i, LinkFamily.choiceValue f i, LinkFamily.choiceTypes f i
  iframe H
  ipureintro
  exact ok i n found

theorem links_alloc nodes f (ok : LinkFamily.ElemOK nodes f) (valid : ✓ LinkFamily.elem nodes f) :
    iprop(⊢ |==> ∃ γ, links capacity γ nodes) := by
  imod iOwn_alloc (E := capacity.link) (LinkFamily.elem nodes f) valid with ⟨%γ, H⟩
  imodintro
  iexists γ
  iapply links_scatter capacity γ nodes f ok $$ H

theorem fullLinks_alloc nodes values : iprop(⊢ |==> ∃ γ, fullLinks capacity γ nodes values) := by
  imod iOwn_alloc (E := capacity.link) (LinkSupply.fullMap nodes values)
    (LinkSupply.fullMap_valid nodes values) with ⟨%γ, H⟩
  imodintro
  iexists γ
  unfold fullLinks
  iunfold LinkSupply.fullMap at H
  iapply own_map_scatter (M := InodeMap) capacity γ _ nodes $$ H

variable (topCapacity : FsTop.Capacity GF)

theorem boot_alloc_at left right f (ok : LinkFamily.ElemOK left f) (valid : ✓ LinkFamily.elem left f) :
    iprop(⊢ |==> ∃ gl gt, FsTop.auth topCapacity gt right ∗
      FsTop.allFragments topCapacity gt right ∗ links capacity gl left) := by
  imod links_alloc capacity left f ok valid with ⟨%gl, Hl⟩
  imod FsTop.allocate topCapacity right with ⟨%gt, Ha, Hf⟩
  imodintro
  iexists gl, gt
  iframe Ha Hf Hl

theorem boot_alloc_root_slack nodes f root ty (ok : LinkFamily.ElemOK nodes f)
    (valid : ✓ (LinkFamily.elem nodes f • FsLink.tokElem root ty)) :
    iprop(⊢ |==> ∃ gl gt, FsTop.auth topCapacity gt nodes ∗
      FsTop.allFragments topCapacity gt nodes ∗ links capacity gl nodes ∗ FsLink.tok capacity gl root ty) := by
  imod iOwn_alloc (E := capacity.link) (LinkFamily.elem nodes f • FsLink.tokElem root ty) valid with ⟨%gl, H⟩
  ihave ⟨Hl, Htok⟩ := (iOwn_op (E := capacity.link)).mp $$ H
  ihave Hl := links_scatter capacity gl nodes f ok $$ Hl
  imod FsTop.allocate topCapacity nodes with ⟨%gt, Ha, Hf⟩
  imodintro
  iexists gl, gt
  iframe Ha Hf Hl
  have same : iOwn (E := capacity.link) gl (FsLink.tokElem root ty) =
      FsLink.tok capacity gl root ty := rfl
  iapply (BIBase.BiEntails.of_eq same).mp $$ Htok

theorem boot_alloc nodes f (ok : LinkFamily.ElemOK nodes f) (valid : ✓ LinkFamily.elem nodes f) :
    iprop(⊢ |==> ∃ gl gt, FsTop.auth topCapacity gt nodes ∗
      FsTop.allFragments topCapacity gt nodes ∗ links capacity gl nodes) :=
  boot_alloc_at capacity topCapacity nodes nodes f ok valid

theorem boot_alloc_full left right values :
    iprop(⊢ |==> ∃ gl gt, FsTop.auth topCapacity gt right ∗
      FsTop.allFragments topCapacity gt right ∗ fullLinks capacity gl left values) := by
  imod fullLinks_alloc capacity left values with ⟨%gl, Hl⟩
  imod FsTop.allocate topCapacity right with ⟨%gt, Ha, Hf⟩
  imodintro
  iexists gl, gt
  iframe Ha Hf Hl

theorem linkBootActual : LinkBootSpec capacity topCapacity where
  independent := boot_alloc_at capacity topCapacity
  rootSlack := boot_alloc_root_slack capacity topCapacity

end MachCSL.Logic.FsState
