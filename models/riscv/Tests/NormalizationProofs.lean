import LeanPaperStock.Specialization
import Lean.Util.CollectAxioms

open Sail Sail.ConcurrencyInterfaceV1

/-- Each pure helper after an effectful read can be named without changing the tree. -/
theorem normalizePureArgument (read : SailM α) (helper : α → Unit) (next : SailM β) :
    (read >>= fun x => (pure (helper x) >>= fun (_ : Unit) => next)) =
    (do let x ← read; let _ := helper x; next) := rfl

#print axioms normalizePureArgument

open Lean Elab Command in
run_cmd do
  for axiomName in ← collectAxioms ``normalizePureArgument do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "unapproved axiom {axiomName} in normalization proof"

/- Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account. -/
