import Xv6.Fs.TreeDiskDefs
import Xv6.Fs.TreeProofs
import Xv6.Fs.ValidityProofs

namespace Xv6.Fs

theorem nodeAt_live image sb i (live : (dinode image sb i).typeZ ≠ 0) :
    nodeAt image sb i = some (nodeOf (dinode image sb i) (fileData image sb i)) := by
  simp only [nodeAt, fileData, beq_eq_false_iff_ne.mpr live, Bool.false_eq_true, ↓reduceIte]

theorem nodeAt_free image sb i (free : (dinode image sb i).typeZ = 0) : nodeAt image sb i = none := by
  simp only [nodeAt, free, BEq.rfl, ↓reduceIte]

theorem nodesUpto_lookup_out image sb (n : Nat) (i : Int) (outside : i < 0 ∨ (n : Int) ≤ i) :
    (nodesUpto image sb n)[i]? = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [nodesUpto]
    cases nodeAt image sb (n : Int) with
    | none => exact ih (by omega)
    | some node =>
      rw [Std.ExtTreeMap.getElem?_insert]
      simp only [Std.compare_eq_eq_iff_eq, show (n : Int) ≠ i by omega, ↓reduceIte]
      exact ih (by omega)

theorem nodesUpto_lookup image sb (n : Nat) (i : Int) (bound : 0 ≤ i ∧ i < (n : Int)) :
    (nodesUpto image sb n)[i]? = nodeAt image sb i := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [nodesUpto]
    by_cases equal : i = (n : Int)
    · subst i
      cases h : nodeAt image sb (n : Int) with
      | none => exact nodesUpto_lookup_out image sb n _ (Or.inr (by omega))
      | some node => simp only [Std.ExtTreeMap.getElem?_insert, Std.compare_eq_eq_iff_eq, ↓reduceIte]
    · cases nodeAt image sb (n : Int) with
      | none => exact ih ⟨bound.1, by omega⟩
      | some node =>
        rw [Std.ExtTreeMap.getElem?_insert]
        simp only [Std.compare_eq_eq_iff_eq, show (n : Int) ≠ i by omega, ↓reduceIte]
        exact ih ⟨bound.1, by omega⟩

theorem treeOfDisk_lookup image sb i (bound : 0 ≤ i ∧ i < sb.ninodes) :
    (treeOfDisk image sb).nodes[i]? = nodeAt image sb i :=
  nodesUpto_lookup image sb sb.ninodes.toNat i ⟨bound.1, by omega⟩

theorem treeOfDisk_lookup_out image sb i (outside : i < 0 ∨ sb.ninodes ≤ i) :
    (treeOfDisk image sb).nodes[i]? = none :=
  nodesUpto_lookup_out image sb sb.ninodes.toNat i (by omega)

theorem treeOfDisk_root image sb : (treeOfDisk image sb).root = 1 := rfl

theorem treeEnt_of_disk image sb i name (bound : 0 ≤ i ∧ i < sb.ninodes) :
    treeEnt (treeOfDisk image sb) i name = match nodeAt image sb i with
    | some (.directory entries) => entries[name]?
    | _ => none := by
  unfold treeEnt
  rw [treeOfDisk_lookup image sb i bound]
  rfl

theorem pathAt_disk_dir image sb i name (bound : 0 ≤ i ∧ i < sb.ninodes)
    (directory : (dinode image sb i).typeZ = 1) :
    pathAt (treeOfDisk image sb) i [name] =
    (dirFirst (fileData image sb i) (dirNrec (dinode image sb i).sizeZ) name).map
      (fun k => ((dirInum (fileData image sb i) k).toNat : Int)) := by
  rw [pathAt_singleton, treeEnt_of_disk image sb i name bound,
    nodeAt_live image sb i (by omega)]
  simp only [nodeOf, directory, ↓reduceIte]
  exact dirView_lookup _ _ _

theorem rootValid_node image sb (valid : rootValid image sb = true) :
    nodeAt image sb 1 = some (.directory
      (dirView (fileData image sb 1) (dirNrec (dinode image sb 1).sizeZ))) := by
  have directory := rootValid_type image sb valid
  rw [nodeAt_live image sb 1 (by omega)]
  simp only [nodeOf, directory, ↓reduceIte]

theorem rootValid_tree image sb (valid : rootValid image sb = true) (bound : 1 < sb.ninodes) :
    RootDirectory (treeOfDisk image sb) := by
  refine ⟨dirView (fileData image sb 1) (dirNrec (dinode image sb 1).sizeZ), ?_⟩
  rw [treeOfDisk_root, treeOfDisk_lookup image sb 1 ⟨by omega, bound⟩]
  exact rootValid_node image sb valid

theorem fsimgValid_tree_root image sb (valid : fsimgValid image sb = true) :
    RootDirectory (treeOfDisk image sb) :=
  rootValid_tree image sb (fsimgValid_root image sb valid) (fsimgValid_superblock image sb valid).ninodes

theorem directoryOK_node image sb i dn (ok : DirectoryOK image sb i dn) (directory : dn.typeZ = 1) :
    NodeRep (nodeOf dn (dataOf image dn)) dn (dataOf image dn) :=
  nodeRep_of dn _ (by omega) ok.unique

theorem fsimgValid_tree_inums image sb (valid : fsimgValid image sb = true) :
    InumsOK (treeOfDisk image sb) := by
  intro i node found
  have inside : 0 ≤ i ∧ i < sb.ninodes := by
    by_cases inside : 0 ≤ i ∧ i < sb.ninodes
    · exact inside
    · have eq := treeOfDisk_lookup_out image sb i (by omega)
      rw [eq] at found
      contradiction
  have upper := (fsimgValid_superblock image sb valid).ushort
  constructor <;> omega

theorem fsimgValid_tree_wf image sb (valid : fsimgValid image sb = true) :
    TreeWellFormed (treeOfDisk image sb) :=
  ⟨fsimgValid_tree_inums image sb valid, fsimgValid_tree_root image sb valid⟩

theorem fsimgValid_tree_node_rep image sb i node (valid : fsimgValid image sb = true)
    (found : (treeOfDisk image sb).nodes[i]? = some node) :
    NodeRep node (dinode image sb i) (fileData image sb i) := by
  have inside : 0 ≤ i ∧ i < sb.ninodes := by
    by_cases inside : 0 ≤ i ∧ i < sb.ninodes
    · exact inside
    · rw [treeOfDisk_lookup_out image sb i (by omega)] at found
      contradiction
  rw [treeOfDisk_lookup image sb i inside] at found
  have live : (dinode image sb i).typeZ ≠ 0 := by
    intro free
    rw [nodeAt_free image sb i free] at found
    contradiction
  rw [nodeAt_live image sb i live] at found
  have eq := Option.some.inj found
  rw [← eq]
  by_cases directory : (dinode image sb i).typeZ = 1
  · exact nodeRep_of _ _ live (fsimgValid_dir image sb i valid inside directory).unique
  · simp only [nodeOf, directory, ↓reduceIte, NodeRep]
    exact ⟨live, directory, trivial⟩

theorem pathAt_disk_cons image sb i name path (bound : 0 ≤ i ∧ i < sb.ninodes) :
    pathAt (treeOfDisk image sb) i (name :: path) =
      match (match nodeAt image sb i with
        | some (.directory entries) => entries[name]?
        | _ => none) with
      | some j => pathAt (treeOfDisk image sb) j path
      | none => none := by
  rw [pathAt_cons, treeEnt_of_disk image sb i name bound]
  rfl

theorem pathAt_disk_singleton image sb i name (bound : 0 ≤ i ∧ i < sb.ninodes) :
    pathAt (treeOfDisk image sb) i [name] = match nodeAt image sb i with
      | some (.directory entries) => entries[name]?
      | _ => none := by
  rw [pathAt_singleton, treeEnt_of_disk image sb i name bound]

end Xv6.Fs

open Lean Elab Command in
run_cmd do
  for (name, info) in (← getEnv).constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs.") then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
