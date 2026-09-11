# Operational spinlock annotation and arbitrary-run exclusion

Author: OpenAI Codex subagent `lean_logic_audit`.

The complete operational annotation contract is inhabited by
`SpinlockPool.actual`. `covers` discharges every actual machine transition:
all hart events and blocked arms, UART/PLIC/reset-disk workers, stale harts,
power-off and every actual `BootFacts` power-on witness. No preservation
callback, ghost resource, extra boot premise or pairwise reservation
disjointness is supplied by a client.

`annotate_run` quantifies over every finite actual `PoolSteps` run from an
arbitrary powered-off generation-zero state, retaining its durable medium.
It preserves the exact step count, observations, fork order and erased final
configuration. It supplies a schedule recording the actual selected occurrence
and physical result of each step, proves its annotation unique, and proves
that at most one current-generation hart lies in the full holder window.
The window begins at the successful reserved-zero swap write and ends at the
successful unlock zero write, including all intervening Sail continuations.
`reachable_boundary_exclusion` gives that physical-PC corollary directly for
actual `PoolSteps`, current-generation `.pure ()` expression membership and
PC indices 10–13, without requiring clients to supply labels or a schedule.
No interior-PC corollary,
fairness, progress, erased-trace occurrence uniqueness or final interference
witness is claimed.

The pure invariant retains exact eight-hart occurrence counts, residual plans,
178 owned-register agreements, actual reservations, latest lock/counter bytes,
winning log positions/views, reset disk and all 68 code bytes. Native Iris
authorities are not duplicated. `OwnerPresent` and occurrence uniqueness justify
the selected owner's phase; source `HartStep` supplies untouched other-register,
reservation/view and log-prefix facts. All concrete events discharge the owner,
code and device facts used in the whole-pool assembly theorem.

Code reads use `CodeUnwritten` at every allowed view. Counter reads use actual
latest timestamps and holder view bounds. Counter stores increment modulo
32 bits, record the real append timestamp and preserve the earlier winning
receipt; stored phases deliberately omit the obsolete `counterTime ≤ B` bound.
Blocked exclusive reads clear their reservation, blocked writes retain it,
and the exact non-draining fence is a state identity. Successful lock reads and
conditional writes remain distinct events; failed spinners append one without
changing the current owner or winning position.

Following the independent Fable review, `Transition.hart` includes the graph of
the partial function `nextCursor`. Latest-word pairs and boundary instruction
indices have proved uniqueness; acquisitions and counter stores use pre-log
length plus one. Missing canonical data returns `none`. `transition_functional`
and `scheduled_steps_functional` fix annotations for the same recorded schedule,
while `steps_have_schedule` covers every actual annotated execution.

Validation: 545 Lake jobs pass. A fresh audit of all **424 declarations in 23
owned modules**, including private helpers, opaque theorem bodies and inductive
constructors throughout the logical cones, found only `propext`,
`Classical.choice` and `Quot.sound`; there were no unsafe/partial dependencies
or excluded compiler companions. The coordinator-owned worker/boot/power/boundary
modules were independently reviewed and audited separately (53 declarations
in six modules). See `docs/reviews/spinlock-pool-workers-review.md`.

Audit correction: an earlier local driver omitted opaque theorem bodies from
its separate implementation traversal (its axiom traversal was complete).
The coordinator reran that original checkpoint with explicit
`allowOpaque := true`; all audits reported above use the corrected traversal.
Evidence: `/tmp/xv6-lean-research/SpinlockPoolAudit.lean`,
`spinlock-pool-audit.log`, `SpinlockPoolWorkerPeerAudit.lean` and
`spinlock-pool-worker-peer-audit.log` in the same local research directory.

The explicit interference execution remains a separate final gate obligation.
This machine-code integration result is not the full xv6 kernel port or the
source context-indexed lock API.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
