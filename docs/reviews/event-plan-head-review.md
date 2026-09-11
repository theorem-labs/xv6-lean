# Independent review of exact EventPlan first-event decomposition

Reviewer: OpenAI Codex subagent `lean_logic_audit`, independently reviewing
`artifact_audit`-authored `EventPlanHeadDefs.lean` and `EventPlanHeadProofs.lean`.

Result: **PASS**. `Head` is a proof view indexed by the original free tree, with
an existing `Plan` on the exact continuation. `prefix_head` cases on the actual
ExecPlan prefix; a pure prefix passes directly to its continuation's head,
while each event keeps its residual prefix and monadic continuation. Induction
on Plan proves completeness. The reconstruction proof uses the existing Plan
constructors and register-read/write laws; `plan_iff_head` therefore states an
actual equivalence, not merely a proposed interpreter contract.

All nine forms preserve their relevant data: owned versus universally valued
pin reads, dependent register writes, exact code-read word and `none` metadata,
all relation-indexed mutable/exclusive results, the exclusive snapshot, complete
present-write request and selected mode eligibility, reservation clearing on
write success, and barrier continuations. The memory-head forms retain RAM
and access-kind guards. Relation-indexed continuations do not assume that any
relation successor exists. The inversion lemmas expose these same forms
without inventing a transition for unsupported events.

The pure-plan equivalence is a fact about the finite proof plan; it does not
make a hart `.pure ()` a machine value. Likewise, this layer does not prove
that an actual memory result satisfies the protocol relation, that blocked
reads preserve the old reservation, or that an actual primitive transition
preserves a residual plan. In particular, blocked exclusive reads clear the
reservation and require a proved reindexing lemma in the operational bridge.
Pin reads retain a symbolic register file, so that bridge must use agreement
on owned registers, not full-register equality with physical hardware pins.
These limitations are stated accurately in the status file.

The combined build with SpinlockWP passes 571 jobs. A fresh physical-origin
audit checked all 23 declarations, including private/generated declarations,
and their full type/body/constructor cones. No nonstandard axioms, unsafe or
partial dependencies occur; zero declarations were excluded. The exported
head/equivalence/inversion proofs use `propext` alone. Evidence:
`/tmp/xv6-lean-research/EventPlanHeadPeerAudit.lean` and
`/tmp/xv6-lean-research/event-plan-head-peer-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
