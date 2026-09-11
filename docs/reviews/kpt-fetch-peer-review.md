# Independent native Sv39 instruction-fetch review

Verdict: PASS for all fifteen contracts. The coordinator read all sixteen
final modules, the exact source-resource definitions and eleven edge checks.
A fresh exporting-disabled audit checked all287 physical declarations,
including private declarations, types, full opaque bodies and constructor
cones. Only the standard three axioms occur; no unsafe/partial dependency
and zero exclusions. Owner build:1,029 jobs; eleven kernel checks passed.

The native half rule derives mapping and physical pristine bytes from the
actual virtual RX window, invokes full residue-derived translation, then
executes the real physical instruction read. Branch-specific A/D facts remain
inside their real guards; each instruction-memory event adds its actual guard.
The closed residue contains the resulting coherent TLB and reservation state.

Full fetch retains the exact generated register/extension/alignment prefix
and both chunk branches. Four-aligned compressed instructions own/read four
bytes; merely two-aligned compressed instructions own/read two. A base
instruction crossing a page boundary uses two independently translated halves,
including unrelated physical pages. The native plan fold internally discharges
each chunk; no chunk WP, physical read or success oracle is a client premise.
All cells, instruction resources, reservations and receipts are threaded.

The concatenation contract uses explicit BitVec.append. The initial overloaded
++ expression elaborated with a truncating Sail coercion and was corrected
before proof; no theorem of that erroneous signature was verified. The final
law and nonzero-high-half check retain all32 bits.

This conditional native rule assumes real instruction resources and the
stated owned configuration. It does not establish boot allocation, a whole
translated instruction cycle or the complete source supervisor capability.
Evidence: /tmp/xv6-lean-research/KptFetchRootAudit.lean and
kpt-fetch-root-audit.log; the owner checks are KptFetchChecks.lean.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
