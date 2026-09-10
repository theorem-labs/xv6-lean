import MachCSL
import Xv6
import Lean.Util.CollectAxioms

/-! Audit all project declarations, not merely a handpicked theorem. Imported
Iris adequacy is checked explicitly because it is a critical soundness dependency.
This audits assumptions, not the semantic faithfulness or completeness of a port. -/
open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    let projectModule := (env.getModuleIdxFor? name).any fun idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      mod.toString.startsWith "MachCSL" || mod.toString.startsWith "Xv6"
    if projectModule then
      let axioms ← collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError m!"unapproved axiom {ax} in {name}"
      checked := checked + 1
      if info.isTheorem then theorems := theorems + 1
  if theorems == 0 then
    throwError m!"no project theorems found: empty audit is not success"
  for name in #[``Iris.ProgramLogic.wp_strong_adequacy_gen, ``Iris.fupd_soundness] do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError m!"unapproved axiom {ax} in foundational theorem {name}"
    logInfo m!"foundation {name}: {axioms}"
  logInfo m!"Audited {checked} project declarations including {theorems} theorems. Whole-system closure is a separate gate."
