# Proposed concrete operational annotation for the spinlock image

Author: OpenAI Codex subagent `lean_logic_audit`. This is a Defs/Spec proposal,
not an implemented preservation theorem. It builds on the frozen native
resource callbacks, `SpinlockFamily`, and exact `EventPlanHead` equivalence.
The underlying relation remains `Machine.Step SpinlockImage.image`.

## Annotation data and local control

Use a data-only `Cursor` containing `fetch : Fin 17`, `registers : RegisterFile`,
`reservation : Option Reservation`, and `phase : SpinlockProtocol.Phase`.
A label is either `hart Cursor` or `worker`; the actual expression supplies its
hart ID, generation and current Sail continuation. Do not put a replacement
program, native ghost authority or assumed transition callback in the label.

For `Expr.hart generation cpu program` carrying cursor `c`, require, whenever
that generation is live:

```lean
OwnedMatch (g.registers cpu) c.registers
c.reservation = g.reservations cpu
EventPlan.Plan (SpinlockFetch.CodeRead c.fetch) SpinlockProtocol.relations
  c.registers c.reservation c.phase program
  (fun _ after _ next => ∃ j, SpinlockFamily.Family cpu j after next)
```

Here `OwnedMatch physical symbolic := ∀ r, EventWP.IsOwned r → physical r = symbolic r`.
It deliberately excludes the two hardware pins, because actual PLIC steps
write them and plan pin reads already quantify over every typed value. The
original residual program is indexed by `Plan`; no syntax approximation or
whole-instruction atomicity is used. At `.pure ()`, `EventPlanHead.pure_iff`
recovers the boundary family. Every actual restart clears the reservation,
chooses either clock flag, and installs the existing `SpinlockFamily.cycle_plan`
for the recovered boundary index with reservation `none`.

A live CPU has exactly one pool occurrence, not merely one distinct expression
value. Count live-generation hart occurrences for each of the eight CPUs.
All stale hart occurrences have smaller generations. When power is off every
hart generation is strictly below the next generation; when power is on each
current-generation CPU occurs exactly once. Keep the unique power occurrence
and matching worker labels. Power-on appends the exact existing eleven forks.
This prevents accidentally proving exclusion for one selected occurrence of a
duplicated logical hart.

## Pure state and holder facts

While powered on, require the existing `MemoryOK` and `ReservationsOK`, the
actual reset-Virtio property, and `g.image = loadedRam SpinlockImage.image`.
Use a pure existential word-history witness, separate from native Iris names:

* `LatestWord g a word t := ∀ j < 4, Memory.Latest g.image g.log
  (addressAdd a j) t (nthByte word j)`.
* Code satisfies the coordinator-owned `SpinlockCodeIntegrity.CodeUnwritten`
  predicate. Its all-view/current-flat read lemmas derive the actual instruction
  bytes from the loaded image; do not duplicate that implementation here.
* The lock has one uniform latest timestamp and word zero or one.
* The counter has one uniform latest timestamp `counterTime` and word
  `counterWord`; initially both are zero.
* A pure `owner : Option (CPU × Nat)` selects at most one live holder. Lock word
  zero means `owner = none`; lock word one means an owner exists. Lock's latest
  timestamp is **not** identified with the winning acquisition position.

Derive current physical reads from `Memory.latest_flat` and `MemoryOK`; derive
all permitted view reads from `Memory.read_of_latest`. For a held/loaded/stored
cursor at `(cpu,B,word,time)`, require owner `(cpu,B)`, counter `(word,time)`,
`0 < B`, `B ≤ g.views cpu`, and the exact winning message at `g.log[B-1]?`:
`⟨snapshot lockAddress 4 1#32, hartAgent cpu⟩`. Held and loaded phases additionally
require `time ≤ B`; stored does not. A reserved cursor has a binary old word
and the actual reservation `some (snapshot lockAddress 4 old)`. It has no owner
or counter transfer. Idle also transfers nothing.

The owner's converse is essential: an owner corresponds to the unique live
hart occurrence with a held/loaded/stored phase, including its residual
continuation. Those phases define the holder window, starting at the actual
successful conditional-write event and ending at the actual unlock-write
event. Pure bookkeeping does not duplicate the native Lock camera: the native
invariant remains its sole owner, and this simulation uses only Prop-valued
facts about actual memory, log, views, reservations and annotated occurrences.
No pairwise-disjoint reservation premise is introduced.

This first invariant need not assert `cpu < 2` for every intermediate holder:
exclusion is proved for all eight CPUs. Participant bounds at all instruction
boundaries already follow from `Family`. If an additional no-data-events
corollary for the parked six is wanted at every intermediate continuation,
prove a passive register/code-only certificate for the four reachable
nonparticipant boundary cases (0,1,2,16). Do not pretend that an arbitrary
`Plan`'s terminal family alone excludes transient memory events.

## Required actual-event transport

`EventPlanHead` supplies the shape of each current event. Every operational
lemma also takes the actual `NodeStep`/`HartStep`; it must derive, rather than
assume, the corresponding protocol result:

| Actual event | Required concrete proof |
| --- | --- |
| Owned register read/write | Use `OwnedMatch`, update only the selected typed cell and keep the actual continuation |
| Pin read | Instantiate the universally quantified continuation with the physical pin value |
| Code read | `CodeUnwritten` and `read_code` determine the word at every allowed read view; advance to the actual chosen view and preserve the reservation |
| Ordinary counter read | Held latest word plus `counterTime ≤ B ≤ currentView ≤ chosenView` determines the returned word; advance the actual view and retain reservation |
| Blocked exclusive read | Same program, reservation becomes `none`; reconstruct its exclusive head with this incoming reservation |
| Successful exclusive read | Current lock is binary; install exactly the returned snapshot and reserved phase, advance to actual log top; transfer no holder resource |
| Blocked write | Same residual program, memory, log, view, reservation and phase |
| Reserved-zero write commit | `ReservationsOK` plus exact reserved mode gives current word zero; hence owner absent. Append actual one-word message, choose `B=oldLog.length+1`, transfer owner and counter phase, derive counter timestamp bound from `Latest` |
| Reserved-one write commit | Current word is one; append the actual failed spinner's one-write while preserving the existing owner and its acquisition position |
| Counter store | Mode eligibility fixes loaded phase and exact modular `word+1` payload; append and move to stored with new counter timestamp, dropping the old visibility bound |
| Unlock store | Stored phase identifies the current owner; append zero, clear owner, return idle, preserve the current counter word/time |
| FENCE rw,w | Exact non-draining `fencePost`; retain stored phase and reservation, invent no drain receipt |

Every successful data store preserves all unrelated latest-byte facts using
`latest_append_frame`; affected bytes use `latest_append_new` and the actual
four-byte snapshot/writeBytes bridge. Code/lock/counter disjointness is a
proved constant-address fact, not an added semantic guard. Word timestamps are
bounded by log length using any one of their four present latest bytes.
All other live harts' held counter facts and winning-message receipts must be
framed across each append, including failed spinner writes.

Blocked exclusive reindexing is a small general proof, not an assumption:

```lean
blocked_exclusive_plan
  (head : EventPlanHead.Head reads rel rs rr s (.impure (.readMem n req) k) Q)
  (exclusive : accessExclusive req.access_kind = true) :
  EventPlan.Plan reads rel rs none s (.impure (.readMem n req) k) Q
```

Case on the head; the plain/code cases contradict `exclusive`, and the exclusive
constructor's successful continuation depends only on its new snapshot, not
on incoming `rr`. Scope this lemma to the actual exclusive head and retain its
existing guards and enabled condition.

## Bounded implementation sequence and exported contracts

First implement only `SpinlockPoolDefs/Spec` with the above concrete predicates,
then small proofs of data latest-word current/all-view reads, append frame/new-word,
owned-register agreement, and blocked-exclusive reindexing. Next prove actual
register/pin/restart transport and **one actual exclusive-read/conditional-write
pair** using the complete source guard and snapshot semantics. Freeze/audit
that slice before expanding to all memory/barrier cases.

The intended later contracts are:

```lean
hart_step_preserves
  (inv : PoolInv (left ++ (Expr.hart gen cpu program, Label.hart cursor) :: right, g))
  (live : ThreadLive g gen)
  (step : HartStep g cpu program program' g') :
  ∃ cursor', PoolInv (left ++ (Expr.hart gen cpu program', Label.hart cursor') :: right, g')

covers : AnnotatedPool.Covers SpinlockImage.image transition PoolInv

holder_exclusion (inv : PoolInv config)
  (left : Holds config cpu) (right : Holds config other) : cpu = other
```

`transition` must record the actual head/result classification and label update;
it must not simply take preservation as its own constructor premise. `covers`
is a theorem to construct from all concrete cases, never an input to the
closed application theorem. Lift with the existing exact `AnnotatedPool`
lemmas, retaining step counts, observations, untouched pool occurrences and
fork append order.

Complete coverage includes all UART and PLIC steps, reset-disk steps (including
its wild branch, proved to write no RAM at reset), stale-generation self-loops,
power-off and **every** `PowerStep.on`/BootFacts witness. Power-off makes old
holders inactive without imposing a pre-crash unlock. Power-on retains the
actual durable disk, resets the pure word-history witness and creates fresh
idle labels for all eight harts, plus the three worker labels. No RAM shape or
memory invariant is imposed on the arbitrary powered-off initial state.

The eventual counter accounting should count committed counter-store messages,
not completed releases: between increment and unlock those differ by one.
Operational exclusion, an explicit interference execution, and the final
all-run theorem remain required before calling this the closed two-hart gate.

## Deterministic annotation correction after Fable review

The current `CursorEdge` is a relation-level residual-plan witness. In particular,
the protocol relations deliberately quantify over acquisition positions, counter
words/timestamps and stored timestamps. They do **not** by themselves determine a
unique annotation of a physical execution. The hart transition now additionally
requires the graph of a partial function
`nextCursor g g' cpu program cursor : Option Cursor`. This function uses the actual
pre/post states: acquisition and counter-store positions are `g.log.length + 1`,
the acquired counter pair is the unique pair satisfying `LatestWord` in `g`, and
the restart index is determined by the boundary PC. Failed/blocked events retain
the exact fields required by the actual reservation/log update. Invalid inputs
return `none`; no default byte, timestamp or fetch index certifies an event.

`CursorEdge` remains alongside the graph equation, so actual event labels,
results, guard information and continuations remain explicit. Graph functionality
without a `PoolInv` preservation premise is proved, and the bounded register,
restart, exclusive-read and swap-write transports discharge the graph equation.
A run-annotation uniqueness statement must
also fix the actual scheduled pool occurrence: erasing labels does not by itself
distinguish identical worker expressions at different list positions. The current
bounded checkpoint proves local graph functionality, but not whole-run uniqueness;
the complete `SpinlockPoolSpec`, particularly `covers`, remains uninhabited.

`Holds` already requires power on and the current generation, so stale holders
do not survive a power cycle as live holders. A physical-PC corollary is scoped
to instruction boundaries, where `Family` identifies indices 10 through 13.
No intermediate physical-PC corollary follows merely from a residual `Plan`'s
terminal family; such a claim needs a separate PC-commit invariant. The holder
window itself is defined by the exact phase transitions at the write events.

The checked `swap_write_exclusive` lemma justifies the winner bound
`B ≤ g.views cpu`; weakening that bound is unnecessary. Subsequent coverage
must explicitly frame view growth on reads, the non-draining fence, UART state,
PLIC pin writes, reset-disk memory/log preservation and other harts' append
receipts. These are proof obligations, not callbacks assumed by the contract.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
