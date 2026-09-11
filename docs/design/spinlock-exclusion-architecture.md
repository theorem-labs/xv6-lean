# Operational spinlock exclusion: architecture assessment

Codex's independent assessment after reading the current machine, native WP,
adequacy, and proposed two-hart design. This is a proposed implementation
contract, not a proved invariant. No production architecture was changed.

## Recommendation

Use a concrete annotated-pool simulation for the operational holder window,
while proving resource transfer and `SafeConfiguration` with the existing native
Iris WPs. The simulation annotates actual threads; it does not restrict the
machine transition relation. Its coverage theorem must construct annotations
for **every** actual reachable pool step. Prove the simulation's preservation
clauses from generated event plans and actual machine-step inversions; do not
leave them as callbacks in the closed theorem.

This incurs a pure control-flow proof as well as the Iris resource proof.
Nevertheless it directly expresses the desired PC-and-continuation window and
preserves the existing complete machine state interpretation and worker WPs.
Share generated instruction decompositions, event inversions, and reservation
facts between the two proofs. Do not introduce a second executable instruction
interpreter or a copied AMO semantics.

## What native adequacy actually exposes

`Iris.ProgramLogic.wp_strong_adequacy_gen` already hands the final `stateI` to
its user-supplied final fancy-update continuation. No Iris fork or extra native
invariant-world allocation is needed. Current `MachineAdequacy.not_stuck`
chooses `MachineInterp.stateInterp`, then consumes that final resource to read
`ObservationsOK`. An application-specific final-observer adapter can expose
additional facts already implied by that same interpretation and available
invariants. This adapter alone cannot add a new invariant or derive exclusion
from `SafeConfiguration`.

The interpretation's interface is
`State → Nat → List Observation → Nat → IProp GF`: the last argument is a
thread count. It does **not** receive the expression pool. The native final
callback has the final pool as a pure parameter, but `wptp_postconditions` has
already turned each nonvalue thread's postcondition contribution into `True`.
One cannot extract an arbitrary thread-local proof precondition from its WP.
In particular, existing adequacy does not reveal which hart currently owns a
holder fragment or which intermediate Sail continuation it is executing.

## Generation-indexed interpretation alternative

A state-only annotation could establish the weaker PC corollary by storing,
for the current generation, a single owner and a tie of the form
`∀ cpu, bodyPC (g.registers cpu PC) → owner = some cpu`. It would need an actual
native ownership resource tied to the lock protocol, with fresh era allocation,
plus an extraction proof from its authority. An existential *unrelated* owner
or an assumed pure preservation predicate is insufficient.

There are three substantive integration costs:

1. `DeadThread.threadWP`, `RegisterWP`, `MemoryReadWP`, `EventWP`, restart,
   UART, PLIC, disk, and power proofs instantiate the concrete
   `MachineInterp.irisGS`. Strengthening `stateInterp` changes those WPs.
   Existing rules cannot be transported merely by dropping or framing the
   extra conjunct: every actual successor must restore it. A generic extension
   theorem may package this work, but every preservation field must be proved
   at the concrete event/worker rules before the gate closes.
2. The source product camera's full exclusive authority lives in the lock
   invariant. It cannot simultaneously be copied into a new state-interpretation
   conjunct: native `ExclAuth.auth_op_valid` rejects two authorities. One must
   relocate authority and revise the lock protocol, or allocate a distinct
   annotation camera with proved synchronization. Neither is free source
   fidelity, and any new camera must use a separately reserved registry slot.
3. A PC-only tie does not characterize the stronger holder window. During one
   AMO instruction, the same PC occurs before the exclusive read, after its
   result, and after the conditional write. The returned word may still exist
   only inside the continuation. A state-only predicate cannot recover that
   stage from the PC. Exact continuation tracking would require an additional
   pool instrumentation or simulation anyway.

Every actual PC write needs its relevant frame/entry proof, not only a single
branch instruction. The entry write into the body needs holder evidence; every
release must establish that the releasing hart is outside the body at the
release memory event. PLIC **does write registers**, specifically both hardware
pins on all eight CPUs; prove PC projection preservation from its actual update.
UART and reset-disk steps need their actual frame proofs as well. Old-generation
threads retain their stutter rules, and power-on must cover arbitrary actual
`BootFacts`, not one concrete boot execution.

The interpretation route remains possible for a PC-only checkpoint. It is not
the smaller honest implementation for the currently requested stronger window.
A fractional-PC lock invariant could also support a PC-only observer without
changing `stateInterp`, but would alter PC token splitting/write rules and still
require current-generation invariant-handle coverage and continuation tracking.
It does not remove the central obligation.

## Bounded simulation contracts

The following names are proposals, not existing Lean declarations. Define a
small annotation type with phases for dispatch/park, pending exclusive read,
reserved old word, post-swap success/failure, held body, pending unlock, and
post-unlock. Include the exact read word, snapshot, counters and residual
subplan only where the generated continuation requires them. The actual Sail
program stays in `Expr`; annotations contain proofs relating that exact program
to a residual generated plan.

A first interface should make the following relations explicit:

- `ControlAt image generation cpu phase program registers`: the actual
  generated continuation and relevant register projections implement this
  phase. Cover both clock choices, all counter wraps, independently read pins,
  arbitrary reset counter settings, and the proven universal PMP/reset family.
- `PoolControl image annotation threads g`: every live CPU expression has its
  matching `ControlAt`; current-generation CPU threads are unique by CPU;
  device/power and stale-generation expressions have their actual forms.
- `LockState annotation g`: the current lock word, last observed/reserved words,
  exact reservation snapshots and acquisition/release phase facts agree. A
  failed swap writes one while preserving the separate owner. Counter/history
  facts use modular 32-bit arithmetic and actual commit events.
- `ProtocolInv image annotation threads g`: the conjunction of these concrete
  relations, `MemoryOK`/`ReservationsOK` where needed, code integrity, reset
  Virtio, and the one-owner condition. An initial powered-off state imposes no
  spurious register or RAM restriction.

Prove these bounded lemmas, in this order:

```lean
-- All pure protocol constructor cases, no machine instruction claims yet.
protocolTransition_unique_owner : ProtocolTransition before after →
  UniqueOwner before → UniqueOwner after

-- Exact instruction/event residuals; returned observation and request fields
-- are retained. Each actual nondeterministic arm must be accounted for.
control_step : ControlAt ... → <concrete protocol/state facts> →
  Step image (.hart gen cpu program) g obs next g' forks →
  ∃ phase', <matching actual successor control and protocol transition>

-- Includes every worker, power transition and arbitrary list context.
protocol_pool_step : ProtocolInv image ann threads g →
  PoolStep image (threads, g) obs (threads', g') →
  ∃ ann', ProtocolInv image ann' threads' g'

protocol_pool_steps : initial.power = false → initial.generation = 0 →
  PoolSteps image n ([.power], initial) obs (threads, g) →
  ∃ ann, ProtocolInv image ann threads g

protocol_holder_exclusion : ProtocolInv image ann threads g →
  g.power = true →
  HolderWindow ann threads g cpu₀ → HolderWindow ann threads g cpu₁ → cpu₀ = cpu₁

protocol_body_pc : ProtocolInv image ann threads g → g.power = true →
  bodyPC (g.registers cpu PC) → HolderWindow ann threads g cpu
```

The ellipses are deliberately unimplemented control-state interfaces, not
permitted final assumptions. Before broad proof work, first freeze the phase
datatype and its exact acquisition/unlock boundaries, then prove the small
protocol transition lemma and one actual AMO residual decomposition. This is
a bounded checkpoint that tests whether the shared-plan approach works.

`protocol_pool_step` must be a proved theorem over **all** `PoolStep` arms.
The existing generic `poolSteps_invariant` is not itself a solution: it takes
a preservation premise and only handles a state predicate, whereas this
invariant depends on the whole pool. Prove the list-context lift and induction
for the concrete annotated relation. The final closed gate combines this
operational theorem with the independently discharged native-WP safety and
resource-transfer theorem over the same image and same actual `PoolSteps`.

## Protocol obligations that must remain visible

Exclusive-read success reads the current flat bytes and installs that snapshot;
its blocked arm clears the reader's reservation. Use actual
`conflictingReservations g cpu` and `ReservationsOK g`, not an arbitrary caller
chosen conflict set. While a zero snapshot is reserved, another conflicting
exclusive read cannot install its own snapshot. Conditional-write success
uses reservation agreement to recover the actual old word and clears custody;
blocked writes preserve it. The failed swap's authored write of one must never
be mistaken for ownership acquisition. The holder window starts at successful
conditional-write commit with old word zero and ends at successful unlock
memory commit, not at either instruction's retirement.

The positive witness needs distinct configurations before and after a spinner's
conditional write. While its reservation blocks the other hart's unlock, that
spinner's own write has not yet been appended. After it appends and clears the
reservation, the formerly blocked unlock can proceed. Record both endpoints.

Counter equality to the number of completed releases is false after a counter
store and before its release. A universal counter invariant can count committed
increment stores modulo `2^32`, or use a release count plus an explicit
post-increment in-flight phase. The native read of the transferred counter is
justified by the acquire event's log-top view and the counter's valid timestamp;
`fence rw,w` remains the real non-draining event. No `.aq`-invented extra view
change, store-store premise, or assumed fence drain is needed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
