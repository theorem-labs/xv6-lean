# Supervisor Bare read independent review

Reviewer: OpenAI Codex subagent `/root/lean_logic_audit`, independent of the
coordinator who authored SupervisorBareRead. Result: **PASS for the declared
Bare virtual-address access scope**; no requested code changes.

Read all five frozen modules, STATUS and design, the reused seven-cell
footprint and native Boundary.fold, and pinned source
`HartSMem.v:756–1028` (outer read, translated read and virtual read wrapper).
Compared actual generated `VmemUtils.lean:241–319` and the Bare translation
path to each composed proof. The source pin is xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; generated model is the repository's
pinned LeanPaperStock output from model
`23dcf8fd923eb8a1958795393d2975632aa940b2`.

`program_boundary` retains the actual initial alignment test, checked modular
page split, effective-privilege and translation-mode reads, translateAddr,
outer read, checked physical access and whole-word assembly. The fifteen
reads are four initial effective/mode reads, four translation reads and seven
outer/physical reads. Neither the repeated status/privilege reads nor the
second PMP configuration read is omitted. The single footprint contains each
of the seven keys once, with independently chosen fractions. Prefix widening
preserves every Plan constructor and never invents read permission.

The actual split theorem covers arbitrary aligned 64-bit addresses and adds
no global no-wrap bound. Public `wp_read` obtains alignment from the supplied
context word. Configuration is explicitly Supervisor/SXL2/Bare/MPRV-clear,
TOR RAM, matched readable PMA and disabled HTIF. The proved identity
translation is constructed from actual register reads; no translation WP,
state-preservation predicate or successful read-value callback is a premise.
This is a concrete Bare specialization of the source's regime-parametric
wrapper, not an implementation of its KPT landing relation.

The boundary keeps every successful word/tag tail and the actual error Exit.
The native fold proves success from genuine all-view context/word ownership,
frames the seven register cells across the real read, and restores the same
context/word plus the selected-view receipt in the guarded continuation.
The ordinary event preserves reservations; the public rule does not consume
a reservation fragment or claim a new reservation. Full state/heap metadata
bookkeeping is supplied by the reused native context read rule, rather than
an extra callback. The result is exactly `Ok word` after actual full-word
assembly. All Sail responses remain represented even though the native RAM
proof rules out the erroneous read successor under its ownership premises.

Independent target rebuild passed **548 jobs**. Fresh physical-origin audit
checked all **57 declarations in the five modules**, including private
helpers and transitive opaque bodies (`allowOpaque := true`), types and
inductive constructors. Only `propext`, `Classical.choice`, `Quot.sound`;
no unsafe/partial logical dependency and zero excluded runtime companions.
Evidence: `/tmp/xv6-lean-research/SupervisorBareReadPeerAudit.lean`,
`supervisor-bare-read-peer-audit.log`, `supervisor-bare-read-peer-build.log`.
This review changed no production file.

Base-register address formation/pointer transformation, actual `vmem_read`,
fetched LOAD, KPT/source stack ownership and complete function WP remain
outside this boundary. Whole generated-model/Rocq correspondence remains
separate; this review does not close that project obligation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
