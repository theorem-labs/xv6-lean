import Xv6.Fs.LinkFamilyDefs
import Xv6.Fs.DurableImageNodeProofs
import MachCSL.Logic.FsLinkProofs
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace Xv6.Fs.LinkFamily
open DurableNode DurableImageNode MachCSL.Logic.FsLink Iris Iris.CMRA Iris.Algebra

theorem kind_exists (n : Node) : ∃ value, KindOK n value := by
  cases h : n.isDir
  · exact ⟨.file, h⟩
  · exact ⟨.directory 0, h⟩

theorem multiplicity_zero (n : Node) (zero : n.nlink = 0) : multiplicity n = 0 := by
  simp [multiplicity, Node.orphan, zero]

theorem multiplicity_ge (n : Node) : n.nlink ≤ multiplicity n := by
  unfold multiplicity
  split <;> omega

theorem multiplicity_live_dir (n : Node) (dir : n.isDir = true) (live : n.nlink ≠ 0) :
    multiplicity n = n.nlink + 1 := by
  simp [multiplicity, dir, Node.orphan, live]

theorem tokenless_dot (self target : Int) (orphan : Bool) :
    tokenless self orphan dotName target = orphan := by
  simp [tokenless]

theorem tokenless_self (self : Int) (orphan : Bool) (name : FName) (ndot : name ≠ dotName) :
    tokenless self orphan name self = true := by
  simp [tokenless, ndot]

theorem tokenless_nondot_target (self target : Int) (orphan : Bool) (name : FName)
    (ndot : name ≠ dotName) (ticket : tokenless self orphan name target = false) :
    target ≠ self := by
  intro same
  subst target
  rw [tokenless_self self orphan name ndot] at ticket
  contradiction

theorem tokenless_orphan_dotdot (self target : Int) :
    tokenless self true dotdotName target = true := by
  simp [tokenless]

theorem tokenless_live_nondot (self target : Int) (name : FName) (ndot : name ≠ dotName) :
    tokenless self false name target = decide (target = self) := by
  simp [tokenless, ndot]

theorem entryElem_exempt self orphan name target ty
    (exempt : tokenless self orphan name target = true) :
    entryElem self orphan name target ty = unit := by simp [entryElem, exempt]

theorem entryElem_ticket self orphan name target ty
    (ticket : tokenless self orphan name target = false) :
    entryElem self orphan name target ty = tokElem target ty := by simp [entryElem, ticket]

theorem entryType_dot self parent isd ty :
    EntryTypeOK self parent isd dotName ty ↔
      ∀ p q, ty = .directory p → parent = some q → q = p := by
  simp [EntryTypeOK]

theorem entryType_dotdot self parent isd ty : EntryTypeOK self parent isd dotdotName ty := by
  simp [EntryTypeOK, dotName, dotdotName]

theorem entryType_dot_missing_parent self isd ty : EntryTypeOK self none isd dotName ty := by
  simp [EntryTypeOK]

theorem entryType_name self parent isd name ty
    (ndot : name ≠ dotName) (ndd : name ≠ dotdotName) :
    EntryTypeOK self parent isd name ty ↔
      ty = if isd then .directory self else .file := by
  cases isd <;> simp [EntryTypeOK, ndot, ndd]

theorem markers_empty (n : Node) : MarkersOK n ∅ := by
  intro name impossible
  simp at impossible

theorem exactCount_empty (n : Node) : ExactCount n ∅ ↔
    (n.isDir = true → n.nlink = if n.orphan then 0 else 1) := by
  simp [ExactCount]

theorem entriesElem_no_entries self (n : Node) types (empty : n.dirEntries = ∅) :
    entriesElem self n types = unit := by
  unfold entriesElem
  rw [empty]
  exact BigOpM.bigOpM_empty _

theorem entriesElem_not_dir self (n : Node) types (nd : n.isDir = false) :
    entriesElem self n types = unit :=
  entriesElem_no_entries self n types (by simp [Node.dirEntries, nd])

theorem nodeElem_no_entries self (n : Node) value types (empty : n.dirEntries = ∅) :
    nodeElem self n value types = authElem self (multiplicity n) value := by
  rw [nodeElem, entriesElem_no_entries self n types empty]
  exact Iris.Algebra.MonoidOps.op_right_id

theorem entriesElem_types_congr self (n : Node) types other
    (same : ∀ name target, n.dirEntries[name]? = some target →
      tokenless self n.orphan name target = false → types name = other name) :
    entriesElem self n types = entriesElem self n other := by
  apply BigOpM.bigOpM_eq
  intro name target lookup
  cases h : tokenless self n.orphan name target
  · rw [entryElem_ticket _ _ _ _ _ h, entryElem_ticket _ _ _ _ _ h,
      same name target lookup h]
  · rw [entryElem_exempt _ _ _ _ _ h, entryElem_exempt _ _ _ _ _ h]

theorem elem_empty (f : Choice) : elem ∅ f = unit := BigOpM.bigOpM_empty _

theorem elem_insert (nodes : DurableState.InodeMap) (f : Choice) (i : Int) (n : Node)
    (absent : nodes[i]? = none) :
    elem (nodes.insert i n) f =
      nodeElem i n (choiceValue f i) (choiceTypes f i) • elem nodes f := by
  have bridge : Iris.Std.insert (M := FamilyMap) nodes i n = nodes.insert i n := by
    apply Std.ExtTreeMap.ext_getElem?
    intro j
    simp [Iris.Std.insert, Std.ExtTreeMap.getElem?_alter, Std.ExtTreeMap.getElem?_insert]
  simpa only [elem, bridge] using BigOpM.bigOpM_insert_eq (M' := FamilyMap) (op := CMRA.op)
    (fun j node => nodeElem j node (choiceValue f j) (choiceTypes f j))
    (m := nodes) (i := i) n absent

theorem elem_extract (nodes : DurableState.InodeMap) (f : Choice) (i : Int) (n : Node)
    (found : nodes[i]? = some n) :
    elem nodes f =
      nodeElem i n (choiceValue f i) (choiceTypes f i) • elem (nodes.erase i) f := by
  have bridge : Iris.Std.delete (M := FamilyMap) nodes i = nodes.erase i := by
    apply Std.ExtTreeMap.ext_getElem?
    intro j
    simp [Iris.Std.delete, Std.ExtTreeMap.getElem?_alter, Std.ExtTreeMap.getElem?_erase]
  simpa only [elem, bridge] using BigOpM.bigOpM_delete_eq (M' := FamilyMap) (op := CMRA.op)
    (fun j node => nodeElem j node (choiceValue f j) (choiceTypes f j))
    (m := nodes) (i := i) (x := n) found

theorem elemOK_empty (f : Choice) : ElemOK ∅ f := by
  intro i n impossible
  simp at impossible

theorem elemOK_erase (nodes : DurableState.InodeMap) (f : Choice) (i : Int)
    (ok : ElemOK nodes f) : ElemOK (nodes.erase i) f := by
  intro j n found
  rw [Std.ExtTreeMap.getElem?_erase] at found
  split at found
  · contradiction
  · exact ok j n found

theorem elemOK_insert (nodes : DurableState.InodeMap) (f : Choice) (i : Int) (n : Node)
    (ok : ElemOK nodes f)
    (node : NodeEntOK i n (choiceMarkers f i) (choiceValue f i) (choiceTypes f i)) :
    ElemOK (nodes.insert i n) f := by
  intro j other found
  rw [Std.ExtTreeMap.getElem?_insert] at found
  split at found
  · have same : i = j := Std.compare_eq_eq_iff_eq.mp ‹compare i j = .eq›
    subst j
    cases Option.some.inj found
    exact node
  · exact ok j other found

theorem elem_choice_congr (nodes : DurableState.InodeMap) (left right : Choice)
    (values : ∀ i n, nodes[i]? = some n → choiceValue left i = choiceValue right i)
    (types : ∀ i n, nodes[i]? = some n → ∀ name target,
      n.dirEntries[name]? = some target → tokenless i n.orphan name target = false →
        choiceTypes left i name = choiceTypes right i name) : elem nodes left = elem nodes right := by
  apply BigOpM.bigOpM_eq
  intro i n found
  rw [nodeElem, nodeElem, values i n found,
    entriesElem_types_congr i n _ _ (types i n found)]

theorem imageChoice_markers image sb i : choiceMarkers (imageChoice image sb) i = ∅ := rfl
theorem imageChoice_value image sb i : choiceValue (imageChoice image sb) i = imageValue image sb i := rfl
theorem imageChoice_types_found image sb i name target
    (found : (imageNode image sb i).dirEntries[name]? = some target) :
    choiceTypes (imageChoice image sb) i name = imageValue image sb target := by
  simp [choiceTypes, imageChoice, found]

theorem imageChoice_types_absent image sb i name
    (absent : (imageNode image sb i).dirEntries[name]? = none) :
    choiceTypes (imageChoice image sb) i name = .file := by
  simp [choiceTypes, imageChoice, absent]

theorem imageValue_kind image sb i : KindOK (imageNode image sb i) (imageValue image sb i) := by
  cases h : (imageNode image sb i).isDir <;> simp [imageValue, h, KindOK]

theorem imageNode_isDir image sb i : (imageNode image sb i).isDir = true ↔
    (dinode image sb i).typeZ = 1 := by
  simp only [Node.isDir, Node.typeZ, imageNode_record, beq_iff_eq]

theorem imageNode_dirEntries image sb i (dir : (imageNode image sb i).isDir = true) :
    (imageNode image sb i).dirEntries =
      dirView (dataOf image (dinode image sb i)) (dirNrec (dinode image sb i).sizeZ) := by
  rw [Node.dirEntries, if_pos dir, imageNode_data_all]
  rfl

theorem image_directory_inside image sb nib i (region : regionValid image sb nib = true)
    (bound : 0 ≤ i ∧ i < 16 * (nib : Int))
    (dir : (imageNode image sb i).isDir = true) : 0 ≤ i ∧ i < sb.ninodes := by
  have ty := (imageNode_isDir image sb i).mp dir
  refine ⟨bound.1, ?_⟩
  by_cases inside : i < sb.ninodes
  · exact inside
  · have free := regionFree_spec image sb nib i (regionValid_free _ _ _ region)
      bound.1 (by omega) bound.2
    omega

theorem image_directory_root image sb nib i (valid : fsimgValid image sb = true)
    (region : regionValid image sb nib = true) (bound : 0 ≤ i ∧ i < 16 * (nib : Int))
    (dir : (imageNode image sb i).isDir = true) : i = 1 :=
  fsimgValid_dir_root image sb i valid (image_directory_inside image sb nib i region bound dir)
    ((imageNode_isDir image sb i).mp dir)

theorem image_root_dir image sb (valid : fsimgValid image sb = true) :
    (imageNode image sb 1).isDir = true :=
  (imageNode_isDir image sb 1).mpr (rootValid_type image sb (fsimgValid_root image sb valid))

theorem image_root_nlink image sb (valid : fsimgValid image sb = true) :
    (imageNode image sb 1).nlink = 1 := by
  have h := (fsimgValid_root_link image sb valid).2
  change ((dinode image sb 1).nlink.toNat : Int) = 1 at h
  change (dinode image sb 1).nlink.toNat = 1
  omega

theorem image_root_not_orphan image sb (valid : fsimgValid image sb = true) :
    (imageNode image sb 1).orphan = false := by
  simp [Node.orphan, image_root_nlink image sb valid]

theorem image_root_multiplicity image sb (valid : fsimgValid image sb = true) :
    multiplicity (imageNode image sb 1) = 2 := by
  simp [multiplicity, image_root_dir image sb valid, image_root_nlink image sb valid,
    image_root_not_orphan image sb valid]

theorem image_root_dot image sb (valid : fsimgValid image sb = true) :
    (imageNode image sb 1).dirEntries[dotName]? = some 1 := by
  have count := (fsimgValid_superblock image sb valid).ninodes
  rw [imageNode_dirEntries image sb 1 (image_root_dir image sb valid)]
  exact (fsimgValid_dir image sb 1 valid ⟨by omega, by omega⟩
    ((imageNode_isDir image sb 1).mp (image_root_dir image sb valid))).dot

theorem image_root_parent image sb (valid : fsimgValid image sb = true) :
    parentEntry (imageNode image sb 1) = some 1 := by
  rw [parentEntry, imageNode_dirEntries image sb 1 (image_root_dir image sb valid)]
  exact rootValid_dotdot image sb (fsimgValid_root image sb valid)

theorem image_entry_target image sb i (name : FName) target (valid : fsimgValid image sb = true)
    (inside : 0 ≤ i ∧ i < sb.ninodes)
    (found : (imageNode image sb i).dirEntries[name]? = some target) :
    (0 < target ∧ target < sb.ninodes) ∧ (dinode image sb target).typeZ ≠ 0 := by
  have dir : (imageNode image sb i).isDir = true := by
    cases hd : (imageNode image sb i).isDir
    · simp [Node.dirEntries, hd] at found
    · rfl
  rw [imageNode_dirEntries image sb i dir] at found
  obtain ⟨k, bound, live, _, targetEq⟩ := dirView_lookup_rec _ _ _ _ found
  have ok := fsimgValid_dir image sb i valid inside ((imageNode_isDir image sb i).mp dir)
  have entry := ok.ent k bound live
  simpa only [targetEq] using entry

/-- Pointwise source img_link_elem_ok, with exactly its two boolean premises. -/
theorem image_node_ent_ok image sb nib i (valid : fsimgValid image sb = true)
    (region : regionValid image sb nib = true) (bound : 0 ≤ i ∧ i < 16 * (nib : Int)) :
    NodeEntOK i (imageNode image sb i) (choiceMarkers (imageChoice image sb) i)
      (choiceValue (imageChoice image sb) i) (choiceTypes (imageChoice image sb) i) := by
  refine ⟨imageValue_kind image sb i, markers_empty _, ?_, ?_⟩
  · intro dir
    have root := image_directory_root image sb nib i valid region bound dir
    subst i
    simp [choiceMarkers, imageChoice, image_root_nlink image sb valid,
      image_root_not_orphan image sb valid]
  · intro name target found ticket
    have dir : (imageNode image sb i).isDir = true := by
      cases hd : (imageNode image sb i).isDir
      · simp [Node.dirEntries, hd] at found
      · rfl
    have root := image_directory_root image sb nib i valid region bound dir
    subst i
    rw [imageChoice_types_found image sb 1 name target found]
    have unmarked : decide (name ∈ choiceMarkers (imageChoice image sb) 1) = false := by
      simp [choiceMarkers, imageChoice]
    rw [unmarked]
    by_cases dot : name = dotName
    · subst name
      have targetRoot : target = 1 := by
        rw [image_root_dot image sb valid] at found
        exact (Option.some.inj found).symm
      subst target
      rw [entryType_dot, image_root_parent image sb valid]
      intro p q value parent
      have valueRoot : imageValue image sb 1 = .directory 1 := by
        simp [imageValue, image_root_dir image sb valid]
      rw [valueRoot] at value
      cases value
      exact (Option.some.inj parent).symm
    · by_cases dotdot : name = dotdotName
      · subst name
        exact entryType_dotdot _ _ _ _
      · rw [entryType_name _ _ _ _ _ dot dotdot]
        have notRoot := tokenless_nondot_target 1 target _ name dot ticket
        have count := (fsimgValid_superblock image sb valid).ninodes
        have inside := (image_entry_target image sb 1 name target valid
          ⟨by omega, by omega⟩ found).1
        have targetNotDir : (imageNode image sb target).isDir = false := by
          cases hd : (imageNode image sb target).isDir
          · rfl
          · have root := fsimgValid_dir_root image sb target valid ⟨by omega, inside.2⟩
              ((imageNode_isDir image sb target).mp hd)
            exact False.elim (notRoot root)
        simp [imageValue, targetNotDir]

theorem image_elem_ok image sb nib (valid : fsimgValid image sb = true)
    (region : regionValid image sb nib = true) :
    ElemOK (imageNodes image sb nib) (imageChoice image sb) := by
  intro i n found
  obtain ⟨bound, rfl⟩ := imageNodes_lookup_inv image sb nib i n found
  exact image_node_ent_ok image sb nib i valid region bound

theorem bootImage_elem_ok (h : BootImageWF disk ndisk sb nib cov) :
    ElemOK (imageNodes (blocks disk) sb nib) (imageChoice (blocks disk) sb) :=
  image_elem_ok (blocks disk) sb nib h.image h.region

/-- A live nondot self-entry is exempt even when the name is not "..". -/
theorem ordinary_self_exempt : tokenless 7 false ([120] : FName) 7 = true := by decide

/-- A live dot carries its token; an orphan dot does not. -/
theorem live_dot_ticket : tokenless 7 false dotName 7 = false := by decide
theorem orphan_dot_exempt : tokenless 7 true dotName 7 = true := by decide

/-- Dot-parent consistency is guarded by the existence of "..", including
the transient directory-creation state. -/
theorem absent_parent_allows_directory_value :
    EntryTypeOK 7 none false dotName (.directory 91) := entryType_dot_missing_parent _ _ _

theorem present_parent_rejects_wrong_value :
    ¬EntryTypeOK 7 (some 3) false dotName (.directory 91) := by
  intro bad
  have impossible := (entryType_dot 7 (some 3) false (.directory 91)).mp bad 91 3 rfl rfl
  omega

end Xv6.Fs.LinkFamily

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "Xv6.Fs.LinkFamily." ||
        name.toString.startsWith "_private.Xv6.Fs.LinkFamily" then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} link-family declarations; standard foundational axioms only."
