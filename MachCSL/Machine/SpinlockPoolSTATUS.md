# Operational spinlock annotation: bounded checkpoint

Author: OpenAI Codex subagent `lean_logic_audit`.

The twelve modules `SpinlockPoolDefs`, `Spec`, `Words`, `Head`, `Registers`,
`Exclusive`, `Swap`, `UpdateDefs`, `UpdateProofs`, `UpdateTransports`,
`MemoryTransports` and `StoreTransports` build together (524 Lake jobs).
A fresh audit of all 282 declarations originating
in these modules, including private helpers and full logical dependency cones
with explicit opaque theorem-body and constructor traversal, found only
`propext`, `Classical.choice` and `Quot.sound`; no unsafe/partial logical
dependency or excluded compiler companion was found.

`PoolInv` retains all eight live hart occurrences, actual residual programs,
178 owned-register agreements, exact reservations, latest lock/counter words,
winning messages/views, reset disk and unchanged code. `Holds` checks both
power and current generation. `initial` and `holder_exclusion` are proved;
the latter is conditional on this concrete invariant.

The bounded transports consume actual `Machine.Step` witnesses. They cover
owned/pin register reads, owned writes, restart with either clock flag, PLIC
framing of cursor control, blocked/successful exclusive lock reads and
blocked/successful conditional swap writes. The last includes both old words:
zero acquires at the actual new log position with the actual counter pair;
one appends the spinner's write while retaining the existing owner/position.
The exclusive read and conditional write remain separate events. Latest-word
current/all-view reads, new-word append, untouched-address framing and blocked
exclusive reservation reindexing are ordinary kernel proofs.

The local event set additionally covers code reads via `CodeUnwritten` at every
allowed view, latest-counter reads justified by the holder's timestamp/view
bounds, the exact identity of the non-draining fence, and blocked/successful
counter stores and unlocks. Counter stores increment modulo 32 bits, record the
actual append timestamp, preserve the original winning receipt/view and drop
the no-longer-valid `counterTime ≤ B` bound. Unlock clears the holder phase
only at the successful zero store. Both store effect records retain the
pre-state owner identity for the subsequent other-hart framing proof.

This checkpoint does **not** inhabit `SpinlockPoolSpec`: whole-pool coverage,
other-hart framing, integration with worker/power coverage,
the operational all-run exclusion theorem and interference witness remain.
The relation-level `CursorEdge` alone does not establish unique annotations.
Following the independent Fable review, `Transition.hart` now additionally
requires the graph of `nextCursor`. `latest_word_unique`, `latest_pair_of_word`
and `boundary_index_of_pc` prove canonical data selection; successful acquire
and counter-store timestamps are the actual pre-log length plus one.
`transition_functional` proves unique successor/fork labels for the same selected
occurrence and concrete pre/post step. `read_transition`, `write_transition`,
`restart_transition`, `exclusive_transition` and `reserved_swap_transition`
inhabit this stronger transition for all actual successors in the bounded slice.
Run uniqueness still requires coverage and the same occurrence-indexed schedule.
See `docs/design/spinlock-pool.md`; no intermediate physical-PC exclusion is
claimed from a terminal `Plan` postcondition.

Audit correction: an earlier local driver traversed `ConstantInfo.value?`
without `allowOpaque := true`; its axiom traversal was complete, but its separate
implementation traversal omitted opaque theorem bodies. The coordinator reran
the original 182-declaration checkpoint with explicit opaque traversal, and the
final 282-declaration audit above uses the corrected traversal throughout.

Audit evidence: `/tmp/xv6-lean-research/SpinlockPoolAudit.lean` and
`/tmp/xv6-lean-research/spinlock-pool-audit.log` (local review artifacts).

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
