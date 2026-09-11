# Independent review of the combined spinlock gate



Reviewer: the independent `lean_logic_audit` Codex agent. The coordinator
wrote `SpinlockIntegrationDefs.lean` and `SpinlockIntegrationProofs.lean`.
Both were read completely. Result: **PASS**, with the scope below.

`CertifiedRun` conjoins the same actual `PoolSteps` execution, native
`SafeConfiguration`, and the annotation supplied by `annotate_run`. The
annotation erases to the same final configuration and records exactly the
step count and observations. Uniqueness is correctly relative to the same
occurrence-indexed schedule. It does not claim that an erased state trace
uniquely selects an occurrence schedule. Its holder-exclusion result uses
the established annotated holder window, not an interior-PC test.

`certify` is universal over the actual `Platform`, arbitrary powered-off,
generation-zero initial state, and every actual finite execution. It uses
the already proved closed native safety theorem and whole-pool annotation
theorem, without a client WP, state-preservation callback, or new ghost
allocation premise. `SafeConfiguration` is the actual successor property
for every final thread together with `ObservationsOK` for this same trace.

The two positive-witness theorems intentionally specialize the platform to
`SpinlockWitness.platform`, whose two concrete reservation predicates are
false. `seven_messages_certified` combines the actual composed power-on run
with `certify` at that platform. Its seven message authors, lock zero,
counter two, empty reservations, twelve retained threads, and preserved
initial durable disk all come from the exact witness endpoint. It stops
just after the unlock writes and retains their pending generated
continuations; it does not claim both C-style release functions have
returned. `concrete_certified_run` supplies actual off/generation-zero
initial state data for every device state, so the combined conclusion has
inhabited premises. The seven-write witness is existential, while the
safety/exclusion annotation theorem remains universal.

The coordinator reported the split target build green at 663 jobs. This
review independently ran a fresh physical-origin audit on both compiled
modules: **12 logical declarations, zero exclusions**, including theorem
bodies via `value? (allowOpaque := true)` and inductive constructors. All
logical dependency cones contain only `propext`, `Classical.choice`, and
`Quot.sound`, with no unsafe or partial dependencies. The three exported
proofs were also checked individually with `#print axioms`.

Raw evidence: `/tmp/xv6-lean-research/SpinlockIntegrationPeerAudit.lean` and
`/tmp/xv6-lean-research/spinlock-integration-peer-audit.log`. No production
code changes were requested or made. This gate concerns the concrete test
image; it does not establish the xv6 kernel acquire/release specifications.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
