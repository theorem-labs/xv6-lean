import Xv6.Fs.TreeSpec
import Xv6.Fs.DirentProofs

namespace Xv6.Fs

theorem fileBytes_length data n : (fileBytes data n).length = n := by simp only [fileBytes, List.length_map, List.length_range]

theorem nodeRep_of dn data (live : dn.typeZ ≠ 0) (unique : DirNamesUnique data (dirNrec dn.sizeZ)) :
    NodeRep (nodeOf dn data) dn data := by
  unfold nodeOf
  split
  · exact ⟨‹_›, unique, rfl⟩
  · exact ⟨live, ‹_›, rfl⟩

theorem nodeRep_nodeOf node dn data (rep : NodeRep node dn data) : node = nodeOf dn data := by
  cases node with
  | file bytes =>
    obtain ⟨_, non_directory, rfl⟩ := rep
    simp only [nodeOf, non_directory, ↓reduceIte]
  | directory entries =>
    obtain ⟨directory, _, rfl⟩ := rep
    simp only [nodeOf, directory, ↓reduceIte]

theorem nodeRep_injective n₁ n₂ dn data (left : NodeRep n₁ dn data) (right : NodeRep n₂ dn data) : n₁ = n₂ :=
  (nodeRep_nodeOf n₁ dn data left).trans (nodeRep_nodeOf n₂ dn data right).symm

theorem nodeRep_directory entries dn data (rep : NodeRep (.directory entries) dn data) : dn.typeZ = 1 := rep.1

theorem nodeRep_file bytes dn data (rep : NodeRep (.file bytes) dn data) : dn.typeZ ≠ 1 := rep.2.1

theorem nodeRep_alloc node dn data (rep : NodeRep node dn data) : dn.typeZ ≠ 0 := by
  cases node with
  | file bytes => exact rep.1
  | directory entries => have := rep.1; omega

theorem nodeRep_entry entries dn data name z (rep : NodeRep (.directory entries) dn data)
    (found : entries[name]? = some z) : ∃ k,
    dirFirst data (dirNrec dn.sizeZ) name = some k ∧ DirLive data k ∧
    dirBname data k = name ∧ ((dirInum data k).toNat : Int) = z := by
  rw [rep.2.2] at found
  obtain ⟨k, first, value⟩ := (dirView_lookup_some _ _ _ _).mp found
  exact ⟨k, first, dirFirst_live _ _ _ _ first, dirFirst_name _ _ _ _ first, value⟩

theorem nodeRep_entry_of entries dn data k (rep : NodeRep (.directory entries) dn data)
    (bound : k < dirNrec dn.sizeZ) (live : DirLive data k) :
    entries[dirBname data k]? = some ((dirInum data k).toNat : Int) := by
  rw [rep.2.2]
  exact dirView_live_value _ _ k rep.2.1 bound live

theorem pathAt_nil tree i : pathAt tree i [] = some i := rfl

theorem pathStep_none (tree : FsTree) (path : List FName) : path.foldl (pathStep tree) none = none := by
  induction path with
  | nil => rfl
  | cons name rest ih => exact ih

theorem pathAt_cons tree i name path : pathAt tree i (name :: path) =
    match treeEnt tree i name with
    | some j => pathAt tree j path
    | none => none := by
  unfold pathAt
  simp only [List.foldl_cons, pathStep]
  cases treeEnt tree i name with
  | some j => rfl
  | none => exact pathStep_none tree path

theorem pathAt_append tree i p q : pathAt tree i (p ++ q) =
    match pathAt tree i p with
    | some j => pathAt tree j q
    | none => none := by
  unfold pathAt
  rw [List.foldl_append]
  cases p.foldl (pathStep tree) (some i) with
  | some j => rfl
  | none => exact pathStep_none tree q

theorem pathAt_singleton tree i name : pathAt tree i [name] = treeEnt tree i name := by
  rw [pathAt_cons]
  cases treeEnt tree i name <;> rfl

theorem pathChain_head tree i path : ∃ rest, pathChain tree i path = i :: rest := by
  cases path <;> exact ⟨_, rfl⟩

theorem pathChain_last tree i j path (found : pathAt tree i path = some j) : j ∈ pathChain tree i path := by
  induction path generalizing i with
  | nil => simp only [pathAt_nil, Option.some.injEq] at found; subst i; simp [pathChain]
  | cons name rest ih =>
    rw [pathAt_cons] at found
    unfold pathChain
    cases h : treeEnt tree i name with
    | none => simp only [h] at found; contradiction
    | some k =>
      rw [h] at found
      exact List.mem_cons_of_mem _ (ih k found)

theorem directoriesAcyclic_ne tree i j name (acyclic : DirectoriesAcyclic tree)
    (dot : name ≠ dotName) (dotdot : name ≠ dotdotName) (step : treeEnt tree i name = some j) : i ≠ j := by
  intro eq
  subst j
  apply acyclic i [name] (by simp) (by intro n hn; simpa only [List.mem_singleton.mp hn] using And.intro dot dotdot)
  rw [pathAt_singleton]
  exact step

theorem device_payload_is_preserved :
    nodeOf ⟨3, 0, 0, 0, 1, []⟩ (fun _ => [7]) = .file [7] := rfl

theorem empty_path_preserves_missing_start (i : Int) :
    pathAt ⟨∅, 1⟩ i [] = some i := rfl

theorem missing_node_stops (i : Int) (name : FName) :
    pathAt ⟨∅, 1⟩ i [name] = none := rfl

end Xv6.Fs

open Lean Elab Command in
run_cmd do
  for (name, info) in (← getEnv).constants.toList do
    if info.isTheorem && (name.toString.startsWith "Xv6.Fs." ||
        name.toString.startsWith "_private.Xv6.Fs.") then
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
