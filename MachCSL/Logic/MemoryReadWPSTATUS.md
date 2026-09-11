# Actual nonexclusive RAM-read WPs

`MemoryReadWPDefs/Spec/Proofs/Link` implement direct-constructor native Iris
read rules at paper pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
The source rules are `HartEvents.v:137–280` (value-after-view plain reads
and their fixed-word corollary), with pristine ownership discharged using
`TsoCtx.v:1922–1970`. The complete `HartEvents.v` was read, including its
exclusive, blocked, MMIO and `swp` alternatives.

`ReadRequest` and `ReadResult` are aliases for the actual generated V1
request/result types. Both guards are explicit and exact:
`deviceAddress req.pa = false` and `accessExclusive req.access_kind = false`.
`plain_step` constructs the actual global hart step. `plain_step_inv`
inverts every actual successor, recovering the nondeterministically chosen
view, its current-view/log-length bounds, the actual `ReadsBytes` fact,
exact resumed expression, precise `advanceView` state, and empty observation
and fork lists. It excludes MMIO and both exclusive alternatives only using
the stated guards. It does not modify or replace those machine arms.

`wp_ram_read_plain_ex` retains the source value-after-view order:
for every reachable view there is a readable word satisfying the supplied
predicate. The actual word is identified using checked bytewise
determinism. The rule itself updates the existing TSO view authority,
mints its exact receipt, restores the full fixed state interpretation and
transports the future observation trace through the actual silent step.
Neither log emptiness nor a successor-preservation oracle is a premise.
The live case is justified by the actual generation certificate; stale
generations use an authority-derived death receipt and the proved native
`wp_dead` after the actual dead self-loop.

`plainPremise` is explicitly a conditional native adaptation of the
source callback. It temporarily exposes the original complete
`powerInterp`, where the source exposes `mstate_interp` plus its TSO bundle.
It must return that ORIGINAL state interpretation after the required
later and close its invariant-opening mask. It supplies read facts and
continuation WPs, not a proof of the successor's resource preservation.
The current interface handles direct constructors; it does not claim the
source's general `mctx`/projection/resumption interface.

`wp_ram_read_plain` derives the source fixed-word form: the opened state
chooses one word that must work at EVERY reachable view. This is distinct
from the general predicate form and is not assumed for arbitrary memory.

`wp_ram_read_pristine` is the concrete ownership specialization. It
completely discharges the callback from the actual byte window and
persistent timestamp-zero window. Its guarded continuation receives the
same byte ownership and the chosen-view receipt. It holds for arbitrary
logs and arbitrary CPU views, including instruction fetches, and never
substitutes current-memory reads for the actual TSO read relation.
`wp_ram_read_pristine_mint` additionally accepts full initial timestamp-zero
fragments, pays their native conversion to discarded pristine fragments,
and explicitly returns that persistent window to the continuation.
Writable timestamp fragments are consumed by this conversion; the theorem
does not falsely retain them.

All byte windows retain modular physical-address arithmetic. No no-wrap,
positive-width, or bounded-width assumption is added; width zero remains
valid. The predicates retain the actual generated optional tag/abort result
carrier, while this successful machine arm resumes with `Ok (word, none)`.

`MemoryReadWPSpec` independently states all four rules. The five registry
exports instantiate their proofs at the existing twenty-slot registry and
native invariant names, with the same concrete image, fixed names, whole
trace, empty value type and `MachineInterp.irisGS`. No extra ghost slot or
machine instance is introduced.

Validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.MemoryReadWPLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/MemoryReadWPAudit.lean
```

The 432-job build passes (proof module 1.1 seconds; link 0.8 seconds).
The namespace-wide transitive audit passes all 29 declarations. Audit output is
`/tmp/xv6-lean-research/memory-read-wp-axioms.log`; only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. No `sorry`, custom axiom,
`native_decide`, or `bv_decide` is used.

Exclusive reads require their own reservation authority update, exact
snapshot result and top-view receipt. Their blocked arm must drop the
caller's stale reservation and be handled by guarded induction. MMIO reads
require the actual partial bus-result and device-ownership update. Those
rules, general context/window load gates, instruction-loop WPs and final
kernel adequacy remain separate work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
