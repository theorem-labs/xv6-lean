# Deterministic spinlock annotation review

The coordinator read the three Update modules and the revised Spec. The
Transition.hart constructor now requires the graph of nextCursor, alongside
the exact relation-level event witness and source liveness. The partial
function returns none for unsupported/missing cases, chooses the canonical
latest counter pair and boundary PC index, and fixes commit timestamps to
the actual pre-state log length plus one. It does not use PoolInv as a
constructor premise. Latest byte/word and instruction-address uniqueness
justify the selections. Blocked outcomes follow actual post-reservation or
log-length fields.

The strengthened register, restart, exclusive read and reserved swap theorems
consume real Machine.Step evidence and produce that graph-backed transition.
The functionality theorem fixes successor labels and fork labels for the
same selected occurrence and actual pre/post step. It does not infer an
occurrence-indexed schedule from an erased configuration trace.

Validation: 520-job combined checkpoint build. A fresh coordinator audit of
all 253 declarations in ten physical modules traversed every theorem/opaque
body and constructor dependency: standard three axioms only, no unsafe or
partial dependency, zero exclusions. Review approved. Full selected-hart
memory coverage, other-hart preservation and complete Covers remain open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
