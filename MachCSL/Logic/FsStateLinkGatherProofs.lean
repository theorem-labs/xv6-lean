import MachCSL.Logic.FsStateLinkProofs

namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Iris.CMRA Iris.Algebra Xv6.Fs FsView
variable {GF : BundledGFunctors} (capacity : FsLink.Capacity GF)

/-- Native fixed-name ownership folding with an existing accumulator. -/
theorem own_map_gather {K V : Type} {M : Type → Type} [LawfulFiniteMap M K] [DecidableEq K]
    γ (f : K → V → FsLink.FamilyRA) (m : M V) (acc : FsLink.FamilyRA) :
    iprop(⊢ iOwn (E := capacity.link) γ acc -∗
      bigSepM (M := M) (fun k v => iOwn (E := capacity.link) γ (f k v)) m -∗
      iOwn (E := capacity.link) γ (acc • bigOpM (M' := M) CMRA.op f m)) := by
  induction m using LawfulFiniteMap.induction_on (M := M) generalizing acc with
  | hemp => rw [BigOpM.bigOpM_empty, CMRA.unit_right_id_L]; iintro H _; iexact H
  | hins k v m absent ih =>
    rw [BigSepM.bigSepM_insert absent |>.to_eq, BigOpM.bigOpM_insert_eq _ v absent, CMRA.assoc]
    iintro Ha ⟨Hkv, Hrest⟩
    ihave H := (iOwn_op (E := capacity.link)).mpr $$ [$Ha $Hkv]
    iapply ih (acc • f k v) $$ H Hrest

theorem own_map_scatter {K V : Type} {M : Type → Type} [LawfulFiniteMap M K] [DecidableEq K]
    γ (f : K → V → FsLink.FamilyRA) (m : M V) :
    iOwn (E := capacity.link) γ (bigOpM (M' := M) CMRA.op f m) ⊢
      bigSepM (M := M) (fun k v => iOwn (E := capacity.link) γ (f k v)) m := by
  induction m using LawfulFiniteMap.induction_on (M := M) with
  | hemp => rw [BigSepM.bigSepM_empty.to_eq]; iintro _; iempintro
  | hins k v m absent ih =>
    rw [BigOpM.bigOpM_insert_eq _ v absent, BigSepM.bigSepM_insert absent |>.to_eq]
    iintro H
    ihave ⟨Hkv, Hrest⟩ := (iOwn_op (E := capacity.link)).mp $$ H
    isplitl [Hkv]
    · iexact Hkv
    · iapply ih $$ Hrest

theorem own_map_valid {K V : Type} {M : Type → Type} [LawfulFiniteMap M K] [DecidableEq K]
    γ (f : K → V → FsLink.FamilyRA) (m : M V) :
    bigSepM (M := M) (fun k v => iOwn (E := capacity.link) γ (f k v)) m ⊢
      ⌜✓ bigOpM (M' := M) CMRA.op f m⌝ := by
  induction m using LawfulFiniteMap.induction_on (M := M) with
  | hemp => rw [BigOpM.bigOpM_empty]; iintro _; ipureintro; exact UCMRA.unit_valid
  | hins k v m absent _ =>
    rw [BigSepM.bigSepM_insert absent |>.to_eq, BigOpM.bigOpM_insert_eq _ v absent]
    iintro ⟨Hkv, Hrest⟩
    ihave H := own_map_gather capacity γ f m (f k v) $$ Hkv Hrest
    ihave %valid := iOwn_cmraValid (E := capacity.link) $$ H
    ipureintro; exact valid

theorem linkNode_choice γ i n :
    linkNode capacity γ i n ⊣⊢
      iprop(∃ c : NameSet × (FsLink.IType × (FName → FsLink.IType)),
        ⌜LinkFamily.NodeEntOK i n c.1 c.2.1 c.2.2⌝ ∗
          iOwn (E := capacity.link) γ (LinkFamily.nodeElem i n c.2.1 c.2.2)) := by
  unfold linkNode
  constructor
  · iintro ⟨%markers, %ty, %types, %ok, H⟩
    iexists (markers, (ty, types)); iframe H; ipureintro; exact ok
  · iintro ⟨%c, %ok, H⟩
    iexists c.1, c.2.1, c.2.2; iframe H; ipureintro; exact ok

theorem links_choose γ nodes : links capacity γ nodes ⊢
    iprop(∃ f : LinkFamily.Choice, ⌜LinkFamily.ElemOK nodes f⌝ ∗
      bigSepM (M := InodeMap) (fun i n => iOwn (E := capacity.link) γ
        (LinkFamily.nodeElem i n (LinkFamily.choiceValue f i) (LinkFamily.choiceTypes f i))) nodes) := by
  have choice := map_choose (GF := GF) (M := InodeMap)
    (∅, (FsLink.IType.file, fun _ : FName => FsLink.IType.file))
    (fun i n c => LinkFamily.NodeEntOK i n c.1 c.2.1 c.2.2)
    (fun i n c => iOwn (E := capacity.link) γ (LinkFamily.nodeElem i n c.2.1 c.2.2)) nodes
  refine Entails.trans ?_ choice
  unfold links
  apply BigSepM.bigSepM_mono
  intro i n _
  exact (linkNode_choice capacity γ i n).mp

theorem links_gather γ nodes (acc : FsLink.FamilyRA) :
    iprop(⊢ iOwn (E := capacity.link) γ acc -∗ links capacity γ nodes -∗
      ∃ f, ⌜LinkFamily.ElemOK nodes f⌝ ∗ iOwn (E := capacity.link) γ (acc • LinkFamily.elem nodes f)) := by
  iintro Ha Hlinks
  ihave ⟨%f, %ok, Hlinks⟩ := links_choose capacity γ nodes $$ Hlinks
  iexists f
  isplit
  · ipureintro; exact ok
  · unfold LinkFamily.elem
    iapply own_map_gather (M := InodeMap) capacity γ _ nodes acc $$ Ha Hlinks

theorem links_valid γ nodes : links capacity γ nodes ⊢
    ⌜∃ f, LinkFamily.ElemOK nodes f ∧ ✓ LinkFamily.elem nodes f⌝ := by
  iintro Hlinks
  ihave ⟨%f, %ok, Hlinks⟩ := links_choose capacity γ nodes $$ Hlinks
  ihave %valid := own_map_valid capacity γ _ nodes $$ Hlinks
  ipureintro; exact ⟨f, ok, valid⟩

theorem links_valid_tok γ nodes root ty :
    iprop(⊢ links capacity γ nodes -∗ FsLink.tok capacity γ root ty -∗
      ⌜∃ f, LinkFamily.ElemOK nodes f ∧ ✓ (LinkFamily.elem nodes f • FsLink.tokElem root ty)⌝) := by
  change iprop(⊢ links capacity γ nodes -∗ iOwn (E := capacity.link) γ (FsLink.tokElem root ty) -∗
    ⌜∃ f, LinkFamily.ElemOK nodes f ∧ ✓ (LinkFamily.elem nodes f • FsLink.tokElem root ty)⌝)
  iintro Hlinks Htok
  ihave ⟨%f, %ok, H⟩ := links_gather capacity γ nodes (FsLink.tokElem root ty) $$ Htok Hlinks
  ihave %valid := iOwn_cmraValid (E := capacity.link) $$ H
  ipureintro
  refine ⟨f, ok, ?_⟩
  rw [CMRA.comm]
  exact valid

theorem linkResourceActual (view : View GF) : LinkResourceSpec view capacity where
  packScatter := inode_link_packScatter view capacity
  inode := inode_ghost_iff view capacity
  gather := links_gather capacity
  validToken := links_valid_tok capacity

end MachCSL.Logic.FsState
