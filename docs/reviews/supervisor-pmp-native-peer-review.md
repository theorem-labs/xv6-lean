# Native supervisor PMP peer review

Reviewer: the OpenAI Codex `lean_logic_audit` subagent, independently of the
coordinator who implemented the four native `SupervisorPmp` modules.
Result: **PASS** for the declared physical PMP-check scope.

I read the complete `SupervisorPmp{Defs,Spec,Proofs,Link}` implementation,
the underlying pure TOR geometry lemmas, and pinned
`SmodePte.v:24–165` at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
The source `pmp_config` owns precisely the full `pmpcfg_n` and `pmpaddr_n`
vector cells. Its entry-zero facts are TOR, positive unsigned upper address,
R/W/X permission, and upper coverage of RAM. The root-PPN parameter is
intentionally unused. Later entries, lock bits, and unrelated registers
remain arbitrary. The native existential register file adds no ownership
beyond the two listed cells and indexes exactly those facts.

The partial-register plans retain arbitrary shares for both vector cells.
They replay the generated first-entry path: configuration read, then the
configuration/address reads inside `pmpReadAddrReg`, grain-zero address
selection, actual TOR range matching and permission dispatch, and the
first successful early exit. The finite footprint has exactly two keys;
there is no full 178-cell assertion or fabricated privilege/security read.
The source wrapper's extra privilege/security facts add no generated event.

The width conversion is justified by actual RAM bounds, which imply the
natural width fits in 64 bits. Positivity and range coverage retain the
source meaningful-access hypotheses. Fetch, PTE load, data load and data
store cases are explicit. The native `wp_check` opens the existential
configuration, applies the independently proved single-event RegisterPlan
fold, and restores the same full cells and configuration to the actual
continuation WP in the same generation. The terminal WP is the caller's
real continuation, not a software-correctness oracle for the checked call.
`actual` and `nativeSpec` construct the advertised contract without a new
camera or an assumed PMP grant lemma.

Coordinator's frozen target build: **441 jobs passed**. Independent fresh
physical-module audit: **48** logical declarations in all four
modules, with opaque theorem bodies and inductive constructors traversed.
Only `propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe or
partial logical dependency and zero exclusions. Evidence:
`/tmp/xv6-lean-research/SupervisorPmpNativePeerAudit.lean` and
`supervisor-pmp-native-peer-audit.log`.

This review does not certify virtual translation, a whole supervisor
instruction, or full cross-backend Sail correspondence. The result is the
actual generated supervisor PMP subprogram and its native two-cell WP.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
