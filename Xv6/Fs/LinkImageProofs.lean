import Xv6.Fs.LinkDirectoryProofs
import Xv6.Fs.DurableLinksProofs

/-! FsDurImg §9f–h: actual native image link-family validity, including
the additional root token required by the later durable snapshot. -/
namespace Xv6.Fs.LinkImage
open DurableNode DurableImageNode LinkFamily LinkSupply LinkDirectory
open MachCSL.Logic.FsLink Iris Iris.CMRA Iris.Algebra

theorem image_nonroot_entries_empty image sb nib i (valid : fsimgValid image sb = true)
    (region : regionValid image sb nib = true) (bound : 0 ≤ i ∧ i < 16 * (nib : Int))
    (nonroot : i ≠ 1) : (imageNode image sb i).dirEntries = ∅ := by
  cases dir : (imageNode image sb i).isDir
  · simp [Node.dirEntries, dir]
  · exact False.elim (nonroot (image_directory_root image sb nib i valid region bound dir))

theorem rootTickets_in_all image sb (valid : fsimgValid image sb = true) key :
    tickCount (dirTickets image 1 (dinode image sb 1)) key ≤ linkCount image sb key := by
  apply tickCount_join
  apply List.mem_map.mpr
  have count := (fsimgValid_superblock image sb valid).ninodes
  refine ⟨1, List.mem_range.mpr (by omega), ?_⟩
  change dirTicketsAt image sb 1 = dirTickets image 1 (dinode image sb 1)
  simp only [dirTicketsAt, rootValid_type image sb (fsimgValid_root image sb valid),
    BEq.rfl, ↓reduceIte]

/-- The root's own dot token and its separately retained token occupy the
two units not charged to ordinary nonself directory tickets. -/
theorem root_augmented_tickets_included image sb (nib : Nat)
    (valid : fsimgValid image sb = true) (links : linksEqual image sb = true)
    (regionSize : sb.ninodes ≤ 16 * (nib : Int)) :
    tokens (imageValue image sb) (1 :: 1 :: dirTickets image 1 (dinode image sb 1)) ≼
      supply (imageNodes image sb nib) (imageValue image sb) := by
  apply tokens_included_supply
  intro key positive
  have count := (fsimgValid_superblock image sb valid).ninodes
  by_cases root : key = 1
  · subst key
    refine ⟨imageNode image sb 1, ?_, ?_⟩
    · rw [imageNodes_lookup, if_pos (by constructor <;> omega)]
    · have noTickets := (fsimgValid_root_link image sb valid).1
      have dominated := rootTickets_in_all image sb valid 1
      rw [image_root_multiplicity image sb valid]
      simp only [tickCount_cons, ↓reduceIte]
      omega
  · have notRoot : (1 : Int) ≠ key := Ne.symm root
    simp only [tickCount_cons, if_neg notRoot] at positive ⊢
    have member := tickCount_member _ key positive
    obtain ⟨k, inRange, emitted⟩ := List.mem_filterMap.mp member
    have record := (recTicket_some image 1 (dinode image sb 1) k key).mp emitted
    have rootOK := fsimgValid_dir image sb 1 valid ⟨by omega, by omega⟩
      (rootValid_type image sb (fsimgValid_root image sb valid))
    have target := rootOK.ent k (List.mem_range.mp inRange) record.1
    rw [record.2.2] at target
    have inside : 0 ≤ key ∧ key < sb.ninodes := ⟨by omega, target.1.2⟩
    have nonDir : (dinode image sb key).typeZ ≠ 1 := by
      intro dir
      exact root (fsimgValid_dir_root image sb key valid inside dir)
    refine ⟨imageNode image sb key, ?_, ?_⟩
    · rw [imageNodes_lookup, if_pos (by constructor <;> omega)]
    · have linksExact := linksEqual_at image sb key links inside target.2 nonDir
      have dominated := rootTickets_in_all image sb valid key
      have multBound := multiplicity_ge (imageNode image sb key)
      change ((dinode image sb key).nlink.toNat : Int) = (linkCount image sb key : Int) at linksExact
      change (dinode image sb key).nlink.toNat ≤ multiplicity (imageNode image sb key) at multBound
      omega

theorem root_remaining_entries_included image sb (valid : fsimgValid image sb = true) :
    mapOps 1 (imageNode image sb 1).orphan (choiceTypes (imageChoice image sb) 1)
      ((imageNode image sb 1).dirEntries.erase dotName) ≼
      tokens (imageValue image sb) (dirTickets image 1 (dinode image sb 1)) := by
  rw [imageNode_dirEntries image sb 1 (image_root_dir image sb valid)]
  apply view_ops_incl_tickets
  intro k bound wins _ _
  have found : (imageNode image sb 1).dirEntries[dirBname (dataOf image (dinode image sb 1)) k]? =
      some ((dirInum (dataOf image (dinode image sb 1)) k).toNat : Int) := by
    rw [imageNode_dirEntries image sb 1 (image_root_dir image sb valid)]
    apply (dirView_lookup_some _ _ _ _).mpr
    exact ⟨k, (dirFirst_wins _ _ k bound).mpr wins, rfl⟩
  exact imageChoice_types_found image sb 1 _ _ found

/-- Source img_link_incl keeps the root-no-self premise explicitly; the
exact nondot-self exemption makes it redundant in this inclusion proof. -/
theorem image_link_incl image sb (nib : Nat) (valid : fsimgValid image sb = true)
    (links : linksEqual image sb = true) (_rootSelf : rootNoSelf image sb = true)
    (regionSize : sb.ninodes ≤ 16 * (nib : Int)) :
    entriesElem 1 (imageNode image sb 1) (choiceTypes (imageChoice image sb) 1) •
      tokElem 1 (imageValue image sb 1) ≼
        supply (imageNodes image sb nib) (imageValue image sb) := by
  apply CMRA.Included.trans (y := tokens (imageValue image sb)
    (1 :: 1 :: dirTickets image 1 (dinode image sb 1))) ?_
    (root_augmented_tickets_included image sb nib valid links regionSize)
  change mapOps 1 (imageNode image sb 1).orphan (choiceTypes (imageChoice image sb) 1)
    (imageNode image sb 1).dirEntries • tokElem 1 (imageValue image sb 1) ≼ _
  rw [mapOps_extract _ _ _ _ dotName 1 (image_root_dot image sb valid)]
  have ticket : tokenless 1 (imageNode image sb 1).orphan dotName 1 = false := by
    rw [tokenless_dot, image_root_not_orphan image sb valid]
  rw [entryElem_ticket _ _ _ _ _ ticket,
    imageChoice_types_found image sb 1 dotName 1 (image_root_dot image sb valid)]
  rw [tokens_cons, tokens_cons]
  have reorder (a b : FamilyRA) : (a • b) • a = a • (a • b) := CMRA.comm
  rw [reorder]
  apply CMRA.op_mono (CMRA.inc_refl _)
  exact CMRA.op_mono (CMRA.inc_refl _) (root_remaining_entries_included image sb valid)

/-- Full source five-premise theorem. Native camera validity is its conclusion. -/
theorem image_link_valid image sb nib (valid : fsimgValid image sb = true)
    (region : regionValid image sb nib = true) (links : linksEqual image sb = true)
    (rootSelf : rootNoSelf image sb = true) (regionSize : sb.ninodes ≤ 16 * (nib : Int)) :
    ✓ (elem (imageNodes image sb nib) (imageChoice image sb) • tokElem 1 (imageValue image sb 1)) := by
  have count := (fsimgValid_superblock image sb valid).ninodes
  have found : (imageNodes image sb nib)[(1 : Int)]? = some (imageNode image sb 1) := by
    rw [imageNodes_lookup, if_pos (by constructor <;> omega)]
  apply elem_valid_of_root _ _ 1 (imageNode image sb 1) _ found
  · intro i n lookup nonroot
    obtain ⟨bound, rfl⟩ := imageNodes_lookup_inv image sb nib i n lookup
    exact image_nonroot_entries_empty image sb nib i valid region bound nonroot
  · exact image_link_incl image sb nib valid links rootSelf regionSize

theorem bootImage_link_valid (h : BootImageWF disk ndisk sb nib cov) :
    ✓ (elem (imageNodes (blocks disk) sb nib) (imageChoice (blocks disk) sb) •
      tokElem 1 (imageValue (blocks disk) sb 1)) :=
  image_link_valid (blocks disk) sb nib h.image h.region h.links h.rootSelf h.advertised

end Xv6.Fs.LinkImage

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "Xv6.Fs.LinkImage." ||
        name.toString.startsWith "_private.Xv6.Fs.LinkImage" then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} link-image declarations; standard foundational axioms only."
