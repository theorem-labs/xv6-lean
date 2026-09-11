# Fable 5.1 max review: two-hart spinlock design

Claude Code CLI, requested model `claude-fable-5-1`, effort `max`, tools disabled,
permission mode `dontAsk`. Session `5c78471b-01db-44d2-bebb-214da861bced` completed successfully
in 718,919 ms. The CLI reports Fable as the substantive reviewer and also records
19 output tokens from its auxiliary Haiku model. The supplied material included
the proposed design, actual node rules, JAL safety link and timestamp-map
definitions. It did not include the existing TsoAppendProofs lookup theorem.
This is a design review, not an independent Lean build or audit.

The following review was written by Claude Fable. Its suggestions are assessed
separately in [the Codex disposition](fable-two-hart-disposition.md); in particular,
the proposed release-count invariant and witness endpoints need correction.

---

**Verdict: approve with changes.** The design's account of the sub-instruction semantics matches the supplied Node rules, and I found no claim that would let a false theorem through. I re-derived all seventeen encodings and branch targets by hand and they agree with the table. The problems are two misdirected proof targets, one unverified definition, and several obligations the document names but leaves too loose to close the gate.

### Mistakes and misdirected requirements

- **Visibility is proved from the wrong fact.** The doc asks for release/store ordering under the `rw,w` fence to show the next holder sees the previous counter write. In the supplied rules the AMO's exclusive read sets the hart's view to the current log length, and its conditional write sets the view one past its own append. So the acquirer's view dominates every log position that existed when it read the lock word. The only extra fact needed is that the counter fragment's timestamp is a valid log position, which its persistent message receipt already gives. No store-store ordering is used, and no relation between the counter timestamp and the unlock timestamp is needed. The barrier rule for this gate should be the trivial non-draining `fencePost` step. Leave `ghost_step` off the critical path. The `.aq` bit contributes nothing in this model and the doc should not describe it as supplying the acquire view.

- **The PC-set theorem is a corollary, not the exclusion property.** Membership in the four-word body starts two instructions after the hart already holds the lock, and excluding the unlock word is correct for the stated reason. The invariant, however, must be written against a holder window defined on the pair of PC and generated continuation: from the successful conditional-write arm with a zero snapshot through the successful unlock write event. Prove exclusion on that window and derive the PC-set statement by inclusion. Writing the invariant against the weak set first means rediscovering the window later.

- **The timestamp-map comment is load-bearing and unverified.** `appendTimestamps` assumes the union on `Std.ExtTreeMap` is right-biased. If it is left-biased, written addresses keep stale timestamps and the `TimestampMapOK` bridge is false. That cannot make a false theorem provable, but it sinks the store rule. Make the bias irrelevant by proving and citing a pointwise lemma:

```
(appendTimestamps old nb len).get? a
  = if a ∈ nb then some (len + 1, payNone) else old.get? a
```

If it does not prove, replace the union with an explicit insert fold. Every use of the bridge should cite the lemma, never the comment.

- **Counter law scope is ambiguous.** "Universal counter laws" appears under interference but not under required conclusions. Either add a stated invariant, counter equals number of completed releases modulo two to the thirty-two, to the lock invariant and the conclusions, or drop the phrase.

### Missing obligations and the smallest adequate fixes

- **Choose the exclusion bridge now.** The pure refinement invariant over pool and continuations duplicates the WP proof for every stage of every instruction on two harts, six parked harts, and three device workers. The state-interpretation extension is smaller. Add a component keyed by generation asserting, for the current era's lock ghost, that any CPU whose authoritative PC lies in the body set is the authoritative holder. Only three places pay: the PC write that enters the body must present the holder fragment, the release ghost update must show the releasing CPU's PC is the unlock word, which the hart's WP proof knows because it owns that register, and power-on resets both PCs and reallocates the ghost. Device workers never write hart registers, so they frame it. The concrete missing piece is a native adequacy variant that exposes the final state interpretation, since the doc says the current one extracts only reducibility and `ObservationsOK`. Name that lemma in the doc. This route also handles stale threads for free, because PCs live in the machine state and reset with the era.

- **State the conflict set as a premise.** `NodeStep` takes the conflicting footprint set as a parameter. Refuting the impossible interleaving, where CPU one reads zero while CPU zero holds a zero snapshot, requires that the pool instantiate that parameter from the other harts' reservation fields and that `ReservationsOK` range over the same fields. Write this into the exclusive-read and write rules rather than leaving it implicit in the pool file.

- **Reservation invariant across every worker.** `ReservationsOK` must survive device steps, bus writes, which clear the writing hart's reservation, and the power step. If the JAL interpretation did not already carry it, it is a new interpretation component with its own initialization, not a lemma.

- **Boot facts beyond `mhartid`.** The AMO plan must discharge the atomics-enabled check at reset, and every step needs the machine interrupt-enable bit clear, since pending interrupts stay arbitrary. Both belong in the same `StaticBoot` projection as `mhartid`. The untracked `BootHartId` files in the working tree suggest that projection is under way and the doc should point at them.

- **Witness statement must carry intermediate configurations.** A single `PoolSteps` conclusion with a final state cannot show which arms were taken. Split the witness into three lemmas. After item one, CPU one's continuation is the pending exclusive read with reservation `none` while CPU zero holds the zero snapshot. After item two, CPU zero's continuation is the pending unlock write and the log carries CPU one's authored one. After item three, the log has seven messages, the lock word is zero and the counter word is two. I traced the schedule against the supplied rules and it is consistent. The counter store is not blocked by CPU one's lock reservation because the footprints are disjoint, and the blocked-write arm is exercised by the plain unlock store, not by any AMO write. After a successful exclusive read the AMO's own write cannot be blocked, since a conflicting reservation cannot be installed while ours is live. The generic rule must still prove that arm, as the doc says.

- **Plain reads need a view receipt.** The doc mentions receipts only on writes. Concluding the counter value from a fragment needs a monotone lower bound on the reader's view that is at least the fragment's timestamp. State that the exclusive read and conditional write both emit such a receipt and that it is monotone within an era.

- **Do not call a safety-only checkpoint the gate.** Name it a spinlock safety checkpoint and reserve the gate name for safety, exclusion, and the interference witness together.

### Ownership check on the store primitives

The primitives pay real obligations. `TsoStore` consumes full byte and timestamp fragments over exactly the written footprint and returns full fragments at the new position, so no write is possible without full ownership and no second authority is minted. The equal-domain requirement ties the fragments to the snapshot, which is right. The exclusive-read rule must consume and return the hart's exclusive reservation fragment in both arms, including the blocked arm that clears it. The conditional write consumes the snapshot fragment and derives the old bytes from `ReservationsOK`. That is the right source for the fact that the read result still equals memory, and it is what stops a spinner's write of one from being mistaken for an acquisition. The blocked write arm must return the request and every input resource unchanged so that Löb closes the self-loop. The doc's refusal to identify the latest lock-word author with the holder is correct and necessary.

Two smaller points. The new camera at slot 24 exceeds what this gate needs. An exclusive option-agent authority with an agreeing fragment gives both the holder token and the exclusion bridge above, and keeps `held 0 ∗ held 1 ⊢ False` as a two-line agreement lemma. Keep the source product camera for the later xv6 port. And write out the unlocked invariant state: lock bytes zero at its position, counter bytes at their position, the holder token, and message receipts for both positions.

Nothing in the design is unsound as written. The three changes that must land before implementation are the exclusion-bridge decision, the pointwise timestamp lemma, and the rewritten visibility argument. The rest are obligations the doc already names and should tighten.

---

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
