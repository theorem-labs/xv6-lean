# Independent review of pure spinlock code integrity

Reviewer: OpenAI Codex subagent `lean_logic_audit`, independently reviewing
coordinator-authored `SpinlockCodeIntegrityDefs` and `SpinlockCodeIntegrityProofs`.

Result: **PASS**. `CodeUnwritten` quantifies over every actual log message and
all 68 instruction-byte addresses. `append_data` preserves it for precisely
an actual four-byte lock or counter snapshot, using the proved concrete
footprint separation and the existing writeBytes-outside lemma. The author and
word payload remain arbitrary; no invented store atomicity or no-wrap premise
is added to the machine.

The generic absence lemmas show that every positive log position contributes
`none` at an untouched byte and that readDown therefore returns the image byte,
independently of visibility/forwarding and chosen view. `read_code` combines
this with the actual loaded-image byte certificates for all seventeen words.
`flat_code` uses the real top-view/flat equivalence to establish a current
physical read. These are exact conditional pure facts; no all-pool preservation
or automatic protection from arbitrary writes is claimed.

The combined replay with closed safety passes 609 jobs. A fresh physical-origin
audit checked all 8 declarations and full type/body/inductive-constructor cones.
Only standard foundational axioms occur, with no unsafe/partial dependency and
zero exclusions. Evidence:
`/tmp/xv6-lean-research/SpinlockCodeIntegrityPeerAudit.lean` and
`/tmp/xv6-lean-research/spinlock-code-integrity-peer-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
