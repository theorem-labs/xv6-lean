# Independent review of the regime cycle shell

Verdict: PASS for the six pure and five native shell contracts. The coordinator
read all six frozen modules and the source correspondence design, then ran a
fresh audit with exporting disabled. All 149 physical declarations were
checked through types, full opaque bodies and constructors: only propext,
Classical.choice and Quot.sound; no unsafe/partial dependency; zero exclusions.

The fifty-cell common partition is reversible and excludes the translation
cells. Bare owns SATP and both PMP vectors; KPT owns the existing four-cell
residue, including TLB. Native mstatus/SIE agreement establishes disabled
interrupts, and the complete pinned GPR file retains the real hart's TP.
The start, successful suffix and restart proofs use actual generated programs,
register plans, retirement and clock rules, preserving the remaining resources.

The active fetch/body WP is an explicit continuation seam. The successful
suffix theorem starts with the actual success constructor and proves no
arbitrary instruction successful. The kernel frame retains real context,
timer and virtual stack resources; it does not construct source sconf,
strans_inv or the complete interrupt capability. Those limits are accurate.

Build: 885 jobs. Independent audit evidence:
`/tmp/xv6-lean-research/MycpuRegimeShellRootAudit.lean` and
`/tmp/xv6-lean-research/mycpu-regime-shell-root-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
