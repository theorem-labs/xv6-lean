# Independent observation-invariant review

Result: **PASS**. Read `ObservationInvariant{Defs,Spec,Proofs,Link}.lean`
against `RiscvPtsto.v:680–723` and `WpUart.v:816–897` at paper pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The ledger is a native invariant containing the existing fixed observation
half and an arbitrary history-indexed client resource. The trivial form
uses the same half with True, which is equivalent to source `obs_pred_triv`.
It does not introduce a second observation ghost name or camera.
Allocation preserves the caller's chosen starting history/resource.

The update requires the invariant namespace to lie inside the current
mask. It opens the invariant, removes the later only under the explicit
Timeless premise for every client history, and uses both observation
halves to identify the stored history with the actual authority. Its
client callback runs at the reduced mask, updates the resource, and
preserves the explicit frame S. Both observation halves move together;
the updated client half and resource close the same invariant before the
authority/frame are returned. No history equality or ownership duplication
is assumed.

The trivial specialization can update to an arbitrary next list because
its client resource is True. This is correctly an ownership rule, not an
assertion that arbitrary history changes correspond to machine events.
Actual state-interp/actor WPs still must derive the precise next history
and observation well-formedness from the actual step. UART output under
loopback, environment input, and power-cycle changes cannot be discarded
by appealing to this invariant alone.

The independent audit `/tmp/xv6-lean-research/ObservationInvariantIndependentAudit.lean`
passed all 18 declarations and their dependency cones, permitting only
`propext`, `Classical.choice`, and `Quot.sound`; output is in
`observation-invariant-independent-axioms.log`. The module was already
built by the owner; this review independently replayed the compiled
namespace audit and read the complete proofs. No correction was required.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
