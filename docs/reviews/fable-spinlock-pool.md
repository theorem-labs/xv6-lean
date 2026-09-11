# Fable 5.1 max review: concrete spinlock annotation

Claude Code CLI, model `claude-fable-5-1`, effort `max`, tools disabled,
permission mode `dontAsk`. Resumed session
`5c78471b-01db-44d2-bebb-214da861bced` completed successfully in 675,590 ms.
The supplied material comprised the operational proposal, prior disposition,
and concrete event, head, family, protocol, machine, annotation, code-integrity
and safety definitions/proofs. This is a review of supplied text; the reviewer
did not run Lean or inspect files independently. The CLI records only Fable
model usage for this invocation.

The review below was written by Claude Fable. See the separate
[Codex disposition](fable-spinlock-pool-disposition.md) for implementation status.

---

**Verdict: approve with changes.** The annotated-pool simulation is the right shape. I walked every arm of the supplied `NodeStep`, every device and power arm of `Step`, and each `Head` constructor against the proposed cursor and pure facts. The invariant is preserved in every case I could check, and no pairwise reservation premise is needed. I found no false invariant for the holder window itself. I found one promised corollary the invariant cannot deliver, one gap that leaves the exported theorem weaker than intended, one bound that depends on an unstated kind fact, and several frame lemmas the document uses without naming.

### Insufficient or unsupported claims

1. **The exported theorem is only as strong as the label update is forced.** `Covers` is existential in the successor label. If `transition` merely asserts that some `WriteStep` or `PlainStep` relates the old and new phase, the free parameters in `acquire` and `increment` let one real run carry several annotations, and "at most one labeled holder" then says less than intended. Fix: define the label update as a function of the old label, the pre-state and the actual event result. The fetch index comes from the boundary PC, `reserved w` from the flat lock bytes, `held` carries `g.log.length + 1` and the unique latest counter pair, and `stored` carries `g.log.length + 1`. Let `transition` be the graph of that function and prove it functional. The annotation of any real run is then unique, and the exported statement can say that the unique annotation labels at most one live hart in the window, where the window opens exactly at a successful `swapWrite` commit from `reserved 0` and closes exactly at a successful `unlockWrite` commit. Do not define `transition` through `PoolInv`. That would make `covers` circular.

2. **The PC-set corollary does not follow mid-instruction.** The cursor ties the physical PC to the symbolic file, but `Plan` constrains only the boundary. Nothing in the invariant says a non-holder's plan never writes a critical-body address into PC before its restart. It is true, but proving it needs per-stage plan structure that the cursor does not carry. State the corollary at instruction boundaries only, where `Family` and `At` give it for indices 10 through 13, and phrase the mid-instruction version on the cursor's fetch index. Withdraw the earlier promise of a physical-PC corollary at every reachable configuration unless a PC-commit fact is added to the cursor.

3. **The holder view bound depends on the write kind.** `B ≤ g.views cpu` holds after the acquire only because the swap's write request is exclusive, which advances the view to `oldLog.length + 1`. The exclusive read alone leaves the view one short of `B`. Either add the checked lemma

```
accessExclusive swapWrite.access_kind = true
```

or weaken the requirement to `t ≤ g.views cpu`, which is all the counter read uses and which the exclusive read alone supplies. The native `won` already carries the receipt at `B`, so the lemma is the smaller change.

4. **`Holds` must check liveness.** A stale label after a power cycle may still read `held`. If `Holds` ignores the generation, exclusion fails across the cycle. The document's window text implies liveness but the contract signature does not show it.

### Coverage, framing and transport

Every row of the event table transports, given facts the document uses but does not name:

- **Views only grow.** Code reads and the counter read choose any view from the current one to the log top. The code-read row omits this view change; add it. The non-draining `fencePost` must be shown to be the identity, or at least monotone, so that `stored` keeps its bound.
- **Workers leave cursor-relevant state alone.** PLIC changes only pin registers, UART changes only its device field, and both leave views, reservations, log and memory untouched. The reset disk step writes no RAM, appends no message, and leaves the device in reset. State these as lemmas on `PlicStep`, `UartStep` and `DiskStep`. The `reserved` premise of `diskLive` then goes unused, which is fine.
- **Conflict set.** The successful read and write arms need the pool's `others` unfolded to the union of the other CPUs' reservation footprints. That is how the acquire commit learns that no other cursor is `reserved`, and how the unlock commit learns the same.
- **Power.** `PowerStep.on` must require power off, or the one-occurrence-per-CPU count fails. Power-on labels need a pure boot `Plan` for every `BootFacts` witness from the reset file to boundary zero. That plan is the only genuinely new plan; the seventeen cycle plans exist.
- **Code reads.** Use `CodeUnwritten` with `read_code` and delete the timestamp-zero alternative from the table so there is one mechanism.

**Framing other harts** reduces to three lemmas and needs no extra state. A step by hart A changes only A's registers, view and reservation plus the shared memory and log. B's cursor, plan and register agreement are untouched. B's holder facts reference only the owner, the counter pair, the receipt at position `B - 1`, and B's own view. The owner changes only at acquire and unlock commits, which need lock word zero and a `stored` phase respectively, so a live holder B blocks both. A cannot store the counter unless A is `loaded`, hence the owner, hence A equals B. What remains is append-left for the receipt, `latest_append_frame` for the counter, and untouched views. A `reserved` cursor's `old` equals the current lock word through `ReservationsOK` without being stored, and it survives A's counter store because the footprints are disjoint.

**Dependent residual transport** is benign. Each `Head` constructor is indexed by the actual first event and its continuation. `NodeStep` fixes the continuation argument, and the constructor's `rest` is universal over relation-approved results, so transport is instantiation plus one rewrite: the owned register value via `OwnedMatch`, the pin value directly, the code word via `read_code`, the counter word via `read_of_latest` with `t ≤ B ≤ view`, and the lock word via `latest_flat`. The only dependent equality is the sigma equation in `exclusiveEnabled`; it yields `n = 4` and the request through `Sigma.mk.inj` and `eq_of_heq`, and `n` must be substituted before `req` is touched. Both the semantics and the `Head` carry `none` read metadata and `Ok none` write results, so no coercion is needed. Blocked arms keep the `Head` and repackage it as a `Plan`; nothing depends on the incoming reservation, and in this program a blocked exclusive read only ever occurs from `idle` with reservation `none`, so `blocked_exclusive_plan` is a repackaging lemma. The relations leave `B`, `v`, `t` and `nextTime` free, so the `Plan` is universal in them; the functional label update, not the relation, is what fixes them to the actual log length and latest counter pair.

Points I checked and found correct: the failed spinner's write preserves the owner, its receipt and the holder's counter facts; `nextTime` exceeds `B` after the counter store, so dropping `t ≤ B` in `stored` is required rather than optional; `At` at indices 8 and 9 correctly uses `x15` to separate the failed and won swap; the acquire commit needs no disjointness invariant because the successful arm's own hypothesis excludes other lock reservations; power-off makes the old holder inactive with no pre-crash unlock; and counting committed counter stores rather than releases is the right accounting.

### Bounded next proof sequence

1. `SpinlockPoolDefs`: `Cursor`, labels, the occurrence-count shape, the pure state, the per-cursor clause, `Holds` with liveness, and the functional label update with `transition` as its graph.
2. `holder_exclusion` and `transition_functional`. Both are short and validate the definitions before any transport is attempted.
3. The initial invariant at `([.power], initial)`, the power-off case, and the four dead-thread self-loops.
4. Frame lemmas for UART, PLIC and reset-disk steps, plus view monotonicity including the non-draining `fencePost`.
5. Register, pin, code-read and restart transport through `EventPlanHead` and `cycle_plan`.
6. One exclusive-read and swap-write pair, both arms of each, both reserved modes, including the `accessExclusive` lemma. Freeze and audit here.
7. Counter read, counter store, fence and unlock, with the append framing lemmas for the other harts.
8. Power-on for every `BootFacts` witness with the boot plan and the eleven labeled forks.
9. `covers`, the lift from `PoolSteps` to `ASteps`, the exported run theorem on the unique annotation, and the boundary PC corollary.

Attempt the seven-message interference witness only after step 9, so its intermediate configurations can be stated with the same labels and checked against the same invariant.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
