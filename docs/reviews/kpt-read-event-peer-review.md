# Shared ordinary PTE event: independent review

PASS for all seven frozen `KptReadEvent` modules: Defs, Spec, Pure, Access,
Power, Proofs and Link. The artifact agent read the complete implementation
independently of its coordinator author. I authored some existing ownership
and native read dependencies, previously reviewed separately by other agents;
this report distinguishes the new composition review from those reviews.

Source pin: `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. I compared the core with
`iris/HartSKpt.v:125–153` (pinned all-view bytes), `160–205` (exact nonleaf and
canonical leaf assembly), `253–309` (one invariant opening and complete path
restoration), and the following `kpt_obl`/predicate-indexed read seam. The
new proof stops at the real eight-byte native RAM event; PMA/PMP and generated
PTE wrapper composition are intentionally separate.

The level selection covers exactly 0, 1 and 2. Canonical snapshot agreement
preserves both raw upper words and all three slot addresses. Access returns
an existential current physical slot with a real full-tree reconstruction
wand. `ReadFact` preserves canonical equality and exact equality when the
reference is a nonleaf; the all-view allowed-byte proof composes those facts
without fixing one leaf value across views.

`power_reads` opens the shared native invariant at the actual pre-event
state, agrees the client's bound with the invariant bound, and uses the real
machine TSO interpretation and credential. It restores the original power
interpretation, every slot, mapping authority, snapshot and bound, then
closes the same invariant. It returns a theorem quantified over each chosen
view separately. The stronger lower-bound-only helper quantification is
proved by the existing pin rule; the public ordinary event retains the
machine's upper-view guard.

The WP proof calls the actual native plain-read rule. Invariant closure
precedes the top-to-empty mask transition. The guarded continuation returns
the actual chosen-view receipt, original reservation and all persistent
clients, and runs the supplied residual on exactly `Ok (word, none)`.
No open invariant or physical slot crosses the event. Older generations use
the existing actual dead-thread rule. The full dependent request is retained;
only its exact path address, nondevice and nonexclusive guards select this
case. Final `nativeSpec` and `registrySpec` discharge all component specs.

Independent validation: the closed target passed all 729 jobs. The fresh
`/tmp/xv6-lean-research/KptReadEventPeerAudit.lean` audited all 29 physical
declarations across seven modules, including complete types, opaque proof
bodies and constructors. Only `propext`, `Classical.choice`, and `Quot.sound`
occur; zero exclusions and no unsafe or partial dependencies. Logs are
`kpt-read-event-peer-build.log` and `kpt-read-event-peer-audit.log` in that
same research directory. No correction was required.

This establishes an ordinary shared event, not exclusive reread, A/D commit,
a complete walk, TLB coherence, boot publication or translated function
correctness.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
