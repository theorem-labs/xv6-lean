import MachCSL
import Xv6
import Lean.Util.CollectAxioms
import Lean.Compiler.ExternAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Util.Path

/-!
Audit imported project declarations by their defining module's build directory,
including private declarations and declarations in unrelated namespaces.

Axiom checking traverses every logical dependency. The separate implementation
check walks statement and proof/definition cones, stopping at explicitly reviewed
library build directories. Lean's standard primitives and proof opacity are not
mistaken for unbound machine hooks. Pin changes to reviewed libraries require a
new review; this check does not independently certify those library implementations.
The source/import coverage check in tools/check_imports.py is a separate gate.
-/
namespace Xv6Audit
open Lean Elab Command

/-- No whole-system theorem has been closed yet. Only reviewed final roots belong here. -/
def closedRoots : Array Name := #[]

/-- Individually reviewed opaque data constants outside library boundaries. Currently none. -/
def reviewedOpaque : Array Name := #[]

def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Remove exactly the module path, obtaining its physical package build directory. -/
def moduleBuildDir (mod : Name) : IO System.FilePath := do
  let mut path ← realPathNormalized (← findOLean mod)
  for _ in mod.components do
    let some parent := path.parent | throw (IO.userError s!"no module directory for {mod}")
    path := parent
  return path

inductive Origin where
  | project | reviewed | unreviewed
  deriving BEq, Inhabited

structure Policy where
  origins : NameMap Origin

/-- Physical module origins, not declaration-name prefixes, define review boundaries.
The anchors identify this package and pinned Iris/Qq/Batteries/Lean installations;
new dependencies (including Sail) do not receive a blanket exemption. -/
def makePolicy (env : Environment) : CommandElabM Policy := do
  let projectDirs ← #[`MachCSL, `Xv6, `LeanPaperStock].mapM fun m => liftIO (moduleBuildDir m)
  let reviewedDirs ← #[`Init, `Iris.ProgramLogic.Adequacy, `Qq,
      `Batteries.Data.List.Basic].mapM fun m => liftIO (moduleBuildDir m)
  let mut origins := {}
  for mod in env.header.moduleNames do
    let directory ← liftIO (moduleBuildDir mod)
    let origin := if projectDirs.contains directory then Origin.project
      else if reviewedDirs.contains directory then Origin.reviewed
      else Origin.unreviewed
    origins := origins.insert mod origin
  logInfo m!"Reviewed library boundaries (implementation traversal stops here): {reviewedDirs}"
  return ⟨origins⟩

def originOf (policy : Policy) (env : Environment) (name : Name) : Origin :=
  match env.getModuleIdxFor? name with
  | some idx => policy.origins.find? env.header.moduleNames[idx.toNat]! |>.getD .unreviewed
  | none => .unreviewed

/-- Lean generates a partial runtime companion even for total recursive definitions.
Do not seed such companions as logical roots when their total owner is present.
If a companion occurs in a logical dependency cone it is still rejected. -/
def isTotalRecursionCompanion (env : Environment) (info : ConstantInfo) : Bool :=
  match Compiler.isUnsafeRecName? info.name with
  | some owner => match env.find? owner with
    | some (.defnInfo value) => info.isPartial && value.safety == .safe
    | _ => false
  | none => false

def checkAxioms (name : Name) : CommandElabM Unit := do
  for ax in ← collectAxioms name do
    unless allowedAxioms.contains ax do
      throwError m!"unapproved axiom {ax} in {name}"

/-- Reject execution hooks independently of logical axiom checking. A theorem is
opaque by design; an `opaque` proof of a proposition is also allowed, but its
body/dependencies are still traversed. Opaque data needs explicit review. -/
def checkImplementation (env : Environment) (info : ConstantInfo) : CommandElabM Unit := do
  if info.isPartial then
    throwError m!"unreviewed partial declaration {info.name}"
  if info.isUnsafe then
    throwError m!"unreviewed unsafe declaration {info.name}"
  if (Compiler.getImplementedBy? env info.name).isSome then
    throwError m!"unreviewed implemented_by declaration {info.name}"
  if (getExternAttrData? env info.name).isSome then
    throwError m!"unreviewed extern declaration {info.name}"
  if info matches .opaqueInfo _ then
    unless reviewedOpaque.contains info.name do
      unless ← liftTermElabM (Meta.isProp info.type) do
        throwError m!"unreviewed opaque data declaration {info.name}"

/-- Traverse a union of dependency cones once. Statement traversal expands data
and definitions but not theorem proofs; implementation traversal also expands
proofs. Boundary hits are counted rather than silently treated as reviewed bodies. -/
def checkCone (policy : Policy) (env : Environment) (roots : Array Name)
    (includeProofs : Bool) (label : String) : CommandElabM Unit := do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut checked : Nat := 0
  let mut boundaries : Nat := 0
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      let some info := env.find? name | throwError m!"missing dependency {name} in {label} cone"
      if originOf policy env name == .reviewed then
        boundaries := boundaries + 1
      else
        checkImplementation env info
        checked := checked + 1
        pending := pending ++ info.type.getUsedConstants
        if includeProofs || !info.isTheorem then
          if let some value := info.value? (allowOpaque := true) then
            pending := pending ++ value.getUsedConstants
        if let .inductInfo value := info then
          pending := pending ++ value.ctors.toArray
  logInfo m!"{label} cone: checked {checked} declarations; {boundaries} reviewed-library boundary references"

end Xv6Audit

open Lean Xv6Audit in
run_cmd do
  let env := (← getEnv).setExporting false
  let policy ← makePolicy env
  let mut project := #[]
  let mut statements := #[]
  let mut theorems : Nat := 0
  let mut runtimeCompanions : Nat := 0
  for (name, info) in env.constants.toList do
    if originOf policy env name == .project then
      checkAxioms name
      if isTotalRecursionCompanion env info then
        runtimeCompanions := runtimeCompanions + 1
      else
        project := project.push name
        statements := statements ++ info.type.getUsedConstants
      if info.isTheorem then theorems := theorems + 1
  if theorems == 0 then
    throwError m!"no project theorems found: empty audit is not success"
  checkCone policy env statements false "Project statement"
  checkCone policy env project true "Project proof/implementation"
  for name in #[``Iris.ProgramLogic.wp_strong_adequacy_gen, ``Iris.fupd_soundness] do
    checkAxioms name
    logInfo m!"foundation {name}: {← collectAxioms name}"
  for name in closedRoots do
    let some info := env.find? name | throwError m!"missing closed root {name}"
    unless info.isTheorem && originOf policy env name == .project do
      throwError m!"closed root {name} must be a theorem defined in the project package"
    checkAxioms name
    checkCone policy env info.type.getUsedConstants false s!"Closed root {name} statement"
    checkCone policy env #[name] true s!"Closed root {name} proof"
  if closedRoots.isEmpty then
    logInfo "INCOMPLETE: closed whole-system root manifest is empty; no whole-system theorem is certified."
  logInfo m!"Audited {project.size} imported project logical declarations including {theorems} theorems; {runtimeCompanions} total-recursion runtime companions excluded as roots; {closedRoots.size} declared closed roots. Semantic correspondence and source/import coverage remain separate gates."
