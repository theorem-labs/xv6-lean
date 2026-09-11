import MachCSL.Logic.FsLinkProofs
import MachCSL.Logic.FsLinkRegistry
import Lean.Util.CollectAxioms
import Lean.Elab.Command

namespace MachCSL.Logic.FsLink

theorem registryFsLinkSpec : FsLinkSpec registryCapacity := fsLinkSpec registryCapacity

end MachCSL.Logic.FsLink

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "MachCSL.Logic.FsLink." ||
        name.toString.startsWith "_private.MachCSL.Logic.FsLink" then
      count := count + 1
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "Unapproved axiom {axiomName} in {name}"
  logInfo m!"Audited {count} native filesystem-link declarations; standard foundational axioms only."
