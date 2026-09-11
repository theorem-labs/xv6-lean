# Interruptible event plans and native fold

`EventPlanDefs`, `EventPlanSpec`, `EventPlanPrefix`, `EventPlanCombinators`,
`EventPlanProofs` and `EventPlanLink` implement a separate well-founded plan
and its native-Iris WP fold. Existing `EventWP.ExecPlan` is unchanged.
`nativeEventPlanSpec` discharges all five event contracts using their actual
native implementations. `registryEventPlanSpec` uses the shared `FsLink`
registry and supplied invariant names; it allocates no extra world or camera.

The plan tracks the actual residual Sail program, symbolic owned register
file, exact reservation value and client protocol index. Its prefix embeds
existing arbitrary-return `ExecPlan`s, including every hardware-pin result.
`fold_bind` executes such a prefix before its actual monadic continuation.
`Plan.bind` and `Plan.mono` compose plans without changing their events;
`of_execPlan`/`of_returns` retain the reservation and protocol index.
Both `Returns` and result-branching `Plan` helpers support the actual ExceptT
lift/bind operations.

Mutable plain RAM reads, exclusive reads, present writes and barriers are
separate single-event constructors. Reserved writes carry the exact snapshot
and the source's strict extraction bound; ordinary writes impose no width or
access-kind restriction. Per-protocol request predicates identify requests
whose resource callbacks the client supplies. Each constructor proves its
predicate for its actual request. `writeModeEnabled` separately checks the
chosen ordinary/reserved proof mode against the protocol state and reservation.
`Plan.write` supplies that eligibility proof; callbacks are required only for
eligible modes. These predicates add no machine guards. The reason for the
mode refinement is recorded in `docs/reviews/event-plan-mode-disposition.md`.

Mutable plain-read access covers every legal view and every returned word;
its actual post-view receipt selects the next protocol resource. Exclusive
access uses current `readBytes`, the advanced TSO interpretation and separate
snapshot custody. Write access returns the exact updated physical/TSO bundle,
then receives the real post-view receipt. Barrier access is the source
`ghostStep`, with no invented drain receipt. These callback types contain no
WP. `fold_plan` constructs their actual continuation WPs by induction and
routes them through the proved native leaf rules.

The source event rules are `HartEvents.v`'s RAM plain/exclusive reads, present
writes and barriers, as mapped in `MemoryReadWPSTATUS`,
`MemoryExclusiveWPSTATUS`, `MemoryWriteWPSTATUS` and `BarrierWPSTATUS`.
The source pin is `.upstream/xv6iris` arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; no generated instruction or machine
rule is changed by this layer.

Code/pristine resources, the 178 owned CPU register cells and reservation
fragment are carried separately from protocol resources. The terminal is
actual `WP (continuation value)`, which respects the machine's value-free
language. Plain reads and barriers retain reservation custody; successful
writes clear it; successful exclusive reads install their actual snapshot.
Blocked and stale/dead behavior comes from the native leaf implementations.
In particular, exclusive retries clear the reservation, while write retries
retain it. The callbacks stay unopened across blocked retries; no fairness or
termination premise is imposed.

Concrete protocol callbacks remain client obligations. A spinlock must prove
its physical/TSO extraction and restoration, including mutable counter reads
using timestamp/view resources and writes using the full ledger update.
This generic fold does not supply that invariant or a concrete AMO plan.
An AMO requires separate read and write boundaries. Pure annotated-pool
preservation must additionally cover every actual transition, including
blocked retries; it does not follow merely from the native WP theorem.
No two-hart exclusion or closed spinlock gate is claimed here.

Validation: all 470 dependency jobs build; prefix proof 7.1 s, full fold
7.1 s, composition helpers 0.99 s, native link 0.90 s. A fresh physical-origin
audit checked all 130 declarations across the six modules, including private
helpers, and traversed their type/body/constructor dependency cones. Only
`propext`, `Classical.choice` and `Quot.sound` occur; no unsafe or partial
semantic dependency was found, and zero declarations were excluded.
No `sorry`, custom axiom or native decision proof is used.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
