import MachCSL.Logic.FsStateLinkSpec
import MachCSL.Logic.FsStateLinkChoiceProofs
import MachCSL.Logic.FsStateProofs
import Xv6.Fs.LinkFamilyProofs

namespace MachCSL.Logic.FsState
open Iris Iris.Std Iris.BI Iris.CMRA Iris.Algebra Xv6.Fs FsView
variable {GF : BundledGFunctors} (view : View GF) (capacity : FsLink.Capacity GF)

/-- Fold optional ownership only beside an existing accumulator: the empty
map never manufactures ownership at a caller-selected ghost name. -/
theorem own_entries_gather γ (self : Int) orphan (entries : NameMap)
    (types : FName → FsLink.IType) (acc : FsLink.FamilyRA) :
    iprop(⊢ iOwn (E := capacity.link) γ acc -∗
      bigSepM (M := EntryMap) (fun name target =>
        if LinkFamily.tokenless self orphan name target then emp
        else iOwn (E := capacity.link) γ (FsLink.tokElem target (types name))) entries -∗
      iOwn (E := capacity.link) γ (acc • bigOpM (M' := EntryMap) CMRA.op
        (fun name target => LinkFamily.entryElem self orphan name target (types name)) entries)) := by
  induction entries using LawfulFiniteMap.induction_on (M := EntryMap) generalizing acc with
  | hemp =>
    rw [BigOpM.bigOpM_empty, CMRA.unit_right_id_L]
    iintro H _; iexact H
  | hins name target entries absent ih =>
    rw [BigSepM.bigSepM_insert absent |>.to_eq, BigOpM.bigOpM_insert_eq _ target absent]
    cases skip : LinkFamily.tokenless self orphan name target
    · rw [LinkFamily.entryElem_ticket _ _ _ _ _ skip]
      simp only [Bool.false_eq_true, ↓reduceIte]
      iintro Ha ⟨Ht, Hrest⟩
      ihave H := (iOwn_op (E := capacity.link)).mpr $$ [$Ha $Ht]
      have assoc := CMRA.assoc_L (x := acc) (y := FsLink.tokElem target (types name))
        (z := bigOpM (M' := EntryMap) CMRA.op
          (fun name target => LinkFamily.entryElem self orphan name target (types name)) entries)
      rw [assoc]
      iapply ih (acc • FsLink.tokElem target (types name)) $$ H Hrest
    · rw [LinkFamily.entryElem_exempt _ _ _ _ _ skip]
      simp only [↓reduceIte, CMRA.unit_left_id_L]
      iintro H ⟨_, Hrest⟩
      iapply ih acc $$ H Hrest

theorem own_entries_scatter γ (self : Int) orphan (entries : NameMap)
    (types : FName → FsLink.IType) :
    iOwn (E := capacity.link) γ (bigOpM (M' := EntryMap) CMRA.op
      (fun name target => LinkFamily.entryElem self orphan name target (types name)) entries) ⊢
    bigSepM (M := EntryMap) (fun name target =>
      if LinkFamily.tokenless self orphan name target then emp
      else iOwn (E := capacity.link) γ (FsLink.tokElem target (types name))) entries := by
  induction entries using LawfulFiniteMap.induction_on (M := EntryMap) with
  | hemp => rw [BigSepM.bigSepM_empty.to_eq]; iintro _; iempintro
  | hins name target entries absent ih =>
    rw [BigOpM.bigOpM_insert_eq _ target absent, BigSepM.bigSepM_insert absent |>.to_eq]
    iintro H
    ihave ⟨Hentry, Hrest⟩ := (iOwn_op (E := capacity.link)).mp $$ H
    isplitl [Hentry]
    · unfold LinkFamily.entryElem
      split
      · iempintro
      · iexact Hentry
    · iapply ih $$ Hrest

theorem inode_link_pack i n ty types :
    iprop(⊢ FsLink.auth capacity view.link i (LinkFamily.multiplicity n) ty -∗
      entriesAt view capacity i n.orphan n.dirEntries types -∗
      iOwn (E := capacity.link) view.link (LinkFamily.nodeElem i n ty types)) := by
  unfold FsLink.auth entriesAt entTokAt FsLink.tok FsLink.toks LinkFamily.nodeElem LinkFamily.entriesElem
  exact own_entries_gather capacity view.link i n.orphan n.dirEntries types _

theorem inode_link_scatter i n ty types :
    iOwn (E := capacity.link) view.link (LinkFamily.nodeElem i n ty types) ⊢
      FsLink.auth capacity view.link i (LinkFamily.multiplicity n) ty ∗
      entriesAt view capacity i n.orphan n.dirEntries types := by
  unfold LinkFamily.nodeElem LinkFamily.entriesElem FsLink.auth entriesAt entTokAt FsLink.tok FsLink.toks
  iintro H
  ihave ⟨Ha, Hentries⟩ := (iOwn_op (E := capacity.link)).mp $$ H
  isplitl [Ha]
  · iexact Ha
  · ihave Hentries := own_entries_scatter capacity view.link i n.orphan n.dirEntries types $$ Hentries
    iunfold FsLink.tokElem at Hentries
    iexact Hentries

theorem inode_link_packScatter i n ty types :
    iOwn (E := capacity.link) view.link (LinkFamily.nodeElem i n ty types) ⊣⊢
      FsLink.auth capacity view.link i (LinkFamily.multiplicity n) ty ∗
      entriesAt view capacity i n.orphan n.dirEntries types := by
  constructor
  · exact inode_link_scatter view capacity i n ty types
  · iintro ⟨Ha, Ht⟩
    iapply inode_link_pack view capacity i n ty types $$ Ha Ht

theorem entTok_choose self parent orphan isDirectory name target :
    entTok view capacity self parent orphan isDirectory name target ⊣⊢
      iprop(∃ ty, ⌜LinkFamily.tokenless self orphan name target = false →
        LinkFamily.EntryTypeOK self parent isDirectory name ty⌝ ∗
        entTokAt view capacity self orphan name target ty) := by
  unfold entTok entTokAt
  cases skip : LinkFamily.tokenless self orphan name target
  · simp only [Bool.false_eq_true, ↓reduceIte, true_implies]
    constructor
    · iintro ⟨%ty, H, %ok⟩; iexists ty; iframe H; ipureintro; exact ok
    · iintro ⟨%ty, %ok, H⟩; iexists ty; iframe H; ipureintro; exact ok
  · simp only [↓reduceIte, Bool.true_eq_false, false_implies]
    constructor
    · iintro _; iexists FsLink.IType.file; iframe
    · iintro _; iempintro

theorem entToks_choose self parent orphan markers (entries : NameMap) :
    bigSepM (M := EntryMap) (fun name target => entTok view capacity self parent orphan
      (decide (name ∈ markers)) name target) entries ⊢
      iprop(∃ types, ⌜EntryChoicesOK self parent orphan markers entries types⌝ ∗
        entriesAt view capacity self orphan entries types) := by
  have choice := map_choose (GF := GF) (M := EntryMap) FsLink.IType.file
    (fun name target ty => LinkFamily.tokenless self orphan name target = false →
      LinkFamily.EntryTypeOK self parent (decide (name ∈ markers)) name ty)
    (fun name target ty => entTokAt view capacity self orphan name target ty) entries
  refine Entails.trans ?_ choice
  apply BigSepM.bigSepM_mono
  intro name target _
  exact (entTok_choose view capacity self parent orphan (decide (name ∈ markers)) name target).mp

theorem entToks_of_at self parent orphan markers (entries : NameMap) types
    (ok : EntryChoicesOK self parent orphan markers entries types) :
    entriesAt view capacity self orphan entries types ⊢
      bigSepM (M := EntryMap) (fun name target => entTok view capacity self parent orphan
        (decide (name ∈ markers)) name target) entries := by
  unfold entriesAt
  apply BigSepM.bigSepM_mono
  intro name target found
  iintro H
  iapply (entTok_choose view capacity self parent orphan (decide (name ∈ markers)) name target).mpr
  iexists (types name)
  iframe H
  ipureintro
  exact ok name target found

theorem inode_link_iff i n :
    iprop((∃ ty, ⌜LinkFamily.KindOK n ty⌝ ∗
      FsLink.auth capacity view.link i (LinkFamily.multiplicity n) ty) ∗ entToksX view capacity i n) ⊣⊢
      linkNode capacity view.link i n := by
  unfold entToksX linkNode entToks
  constructor
  · iintro ⟨⟨%ty, %kind, Ha⟩, ⟨%markers, %mark, %count, Hentries⟩⟩
    ihave ⟨%types, %choices, Hentries⟩ :=
      entToks_choose view capacity i (LinkFamily.parentEntry n) n.orphan markers n.dirEntries $$ Hentries
    iexists markers, ty, types
    isplit
    · ipureintro; exact ⟨kind, mark, count, choices⟩
    · iapply inode_link_pack view capacity i n ty types $$ Ha Hentries
  · iintro ⟨%markers, %ty, %types, %ok, H⟩
    ihave ⟨Ha, Hentries⟩ := inode_link_scatter view capacity i n ty types $$ H
    isplitl [Ha]
    · iexists ty; iframe Ha; ipureintro; exact ok.1
    · iexists markers
      isplit
      · ipureintro; exact ok.2.1
      · isplit
        · ipureintro; exact ok.2.2.1
        · iapply entToks_of_at view capacity i (LinkFamily.parentEntry n) n.orphan markers n.dirEntries types ok.2.2.2 $$ Hentries

theorem inode_ghost_iff i n : inodeGhost view capacity i n ⊣⊢
    linkNode capacity view.link i n ∗ ⌜DurableNode.Local i n⌝ := by
  rw [← (inode_link_iff view capacity i n).to_eq]
  unfold inodeGhost
  constructor
  · iintro ⟨%ty, %kind, Ha, Hentries, Hlocal⟩
    iframe Hentries Hlocal
    iexists ty; iframe Ha; ipureintro; exact kind
  · iintro ⟨⟨⟨%ty, %kind, Ha⟩, Hentries⟩, Hlocal⟩
    iexists ty; iframe Ha Hentries Hlocal; ipureintro; exact kind

theorem ghost_split s : ghost view capacity s ⊣⊢ links capacity view.link s.inodes ∗ pureState s := by
  unfold ghost links pureState
  have splitNode : (fun i n => inodeGhost view capacity i n) =
      (fun i n => iprop(linkNode capacity view.link i n ∗ ⌜DurableNode.Local i n⌝)) := by
    funext i n
    exact (inode_ghost_iff view capacity i n).to_eq
  rw [splitNode, BigSepM.bigSepM_sep_eq]
  constructor
  · iintro ⟨Hp, ⟨Hl, Hlocal⟩, Hg⟩
    iframe Hl Hp Hlocal Hg
  · iintro ⟨Hl, Hp, Hlocal, Hg⟩
    iframe Hp Hl Hlocal Hg

end MachCSL.Logic.FsState
