# Two-hart spinlock integration gate

The gate is closed after independent review. It assembles native safety,
operational exclusion and an inhabited
positive execution over the actual generated Sail model and the checked
68-byte test image. This is a small-program integration theorem; all six
whole-xv6 theorem roots and cross-prover semantic correspondence remain open.

The universal interface is SpinlockIntegration.certify: for every Platform
and every actual finite PoolSteps run from an arbitrary powered-off,
generation-zero state, it proves native SafeConfiguration and a unique
annotation for the recorded occurrence-indexed schedule. That annotation
preserves step count, observations, fork order and the erased final state,
and proves the complete event-defined holder exclusion property.

SpinlockPool.reachable_boundary_exclusion is the direct physical-machine
corollary at completed `.pure ()` instruction boundaries and body PCs 10–13.
It takes no labels or invariant. It makes no mid-instruction PC assertion.
The principal holder window begins at a successful old-zero conditional
write and ends at the successful unlock write, not at retired C-function
returns or counter increments.

SpinlockIntegration.complete_gate is the concrete single positive root.
Its real power-on prefix reaches CPU 0 at body index 10 and proves Holds
there by annotating that execution. The same annotation continues along
the real suffix to seven writes, lock = 0 and counter = 2. Both blocked
access checkpoints are retained in the composed phases. The final pool has
twelve entries, all reservations are clear, and the physical disk is the
original initial medium. Final active expressions retain their exact
post-unlock-write continuations.

The positive witness supplies its explicit Platform and initial state for
every device state. It chooses non-ticking cycles, minimal permitted ordinary
read views, no intermediate power cycle, and leaves CPUs 2–7 unscheduled
at their boot register files. They are not asserted already parked.
Uniqueness is relative to the occurrence-indexed schedule, not an erased
state trace without scheduler choices. No fairness or progress theorem is
claimed. The universal safety/exclusion result has none of these schedule
restrictions.

The final root target builds 666 jobs. Root audits check all 187 release
witness declarations, all 30 holder/gate declarations, and the independent
agent checks the earlier twelve integration declarations. The full repository
build/audit and independent final peer review are recorded in docs/STATUS.md
and docs/reviews. Fable's sixth max-effort review approved the core proofs
and requested holder inhabitation and one root; both are now implemented.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
