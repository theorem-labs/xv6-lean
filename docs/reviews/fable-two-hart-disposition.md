# Codex disposition of Fable's two-hart review

The review approves the design with changes. The design now states the actual
acquire visibility argument: exclusive read reaches the current log top,
timestamp validity bounds the counter's latest position, and conditional write
advances the view beyond its append. Native TsoReadAt proves the subsequent
latest-value read from byte/timestamp ownership and a view receipt. The rw,w
fence stays non-draining; neither its ordering nor the aq bit is credited with
the visibility result.

The primary exclusion property now concerns the holder window on PC and actual
generated continuation, from acquisition's successful write through the unlock
write. The critical-body PC set is only a corollary. The interference witness
has explicit intermediate configurations before reservations are cleared. Two
suggested review endpoints needed correction: the holder's zero snapshot is no
longer live after its swap, and the spinner's one snapshot is no longer live
after its failed-acquisition write of one. The blocked unlock must occur before
that second write commits. The required final witness remains seven messages,
lock zero and counter two.

The requested timestamp lookup lemma was already proved in TsoAppendProofs,
which was absent from the review packet. `appendTimestamps_lookup` states the
exact new-or-old lookup and `timestampMapOK_store` uses it. The native TsoStore
update is independently reviewed, including heap metadata and all untouched
payload arms. It fixes new owned timestamps to payNone, matching phys_ledger.

The source pool already derives conflicts from all other CPU reservations;
Era.interp already carries ReservationsOK. These are explicit obligations of
all new event rules, not new assumed invariants. BootHartId proves the exact
hart selection, while the existing universal reset projections retain enabled
atomics and disabled machine interrupt enables. Generated instruction plans
must still consume those facts.

The proposed counter-equals-completed-releases invariant is not adopted: the
counter changes before the holder releases. The design removes the ambiguous
universal-counter claim and states the modular counter-two witness; any later
universal count must account for completed increments and the pending holder.

The architecture review now selects a concrete annotated-pool simulation for
the stronger holder window; see docs/design/spinlock-exclusion-architecture.md.
Every actual pool step must have a proved annotation successor, and annotation
erasure leaves the machine unchanged. Existing native WPs remain the safety and
resource-transfer proof. Native strong adequacy already exposes final stateI;
our application adapter discards it. A generation-indexed extension would also
need explicit transport of all relevant WP rules, which fix MachineInterp's
current IrisGS instance. It cannot be paid by assumed preservation callbacks.
The review's statement that device workers never write hart registers is too
broad: PLIC writes interrupt pins, though not PCs. Either architecture must prove
that frame. The proposed source product camera remains provisional; simplifying
it for the checkpoint does not discharge the full xv6 lock-camera contract.

Only the foundational store, barrier and read bridges are implemented here.
The design calls a safety-only result a checkpoint; the two-hart gate still
requires closed safety, operational exclusion and the interference witness.
The full compiled xv6 acquire/release contracts and whole-system port remain
open. The review has not been treated as a proof certificate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
