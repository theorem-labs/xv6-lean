# Independent root review: interruptible event composition

Verdict: PASS. Codex root read all six EventPlan modules, including the
resource-only callback interface, generalized prefix proof, event fold,
monadic composition laws and native contract link.

Plans retain register, reservation and protocol indices through actual
free-tree continuations. Every mutable plain-read view/result must be
covered by its callback; exclusive reads use current bytes and the actual
top-view receipt. Writes restore the actual successor interpretation and
choose their next protocol state after the real write receipt. Held-snapshot
writes obtain their readback fact through the native reservation rule.
Enabled predicates select concrete requests, without narrowing the results
that the actual machine can return. Barriers preserve the separate event.

The fold supplies recursive WPs itself. Access callbacks contain resource
transformations and pure branch relations, not an assumed WP or preservation
theorem. Native leaf rules retain their blocked retry, stale-generation,
power and observation obligations. The generalized prefix permits every
hardware-pin result and frames mutable resources through its continuation.

The concrete link discharges all event-rule contracts from previously
proved native rules and uses the same machine/invariant world. It does not
instantiate a lock resource callback, prove annotation preservation or close
the two-hart gate. These remain explicit application obligations.

A fresh separate audit passed for all 130 declarations, including private
helpers and full type/body dependency cones. Only the standard three axioms
occur; no unsafe/partial semantic dependencies and zero exclusions.

The root reread the subsequent mode-eligibility correction in full. The
selected ordinary/reserved mode is now explicitly proved eligible by the
plan and passed to its callback, avoiding a demand for an unused ordinary
callback without readback evidence. The native machine successors and leaf
proofs are unchanged. The corrected fold and combinators preserve this
evidence; see `event-plan-mode-disposition.md` for the concrete finding.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
