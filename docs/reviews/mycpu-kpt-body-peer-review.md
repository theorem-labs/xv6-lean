# MycpuKptBody independent review

Verdict: PASS for thirteen pure and one native indexed-body contracts.
Read all five complete modules and the source instruction/body mapping.
A fresh audit independently checks all 178 physical declarations, types,
opaque bodies and constructors, with standard foundational axioms only,
zero unsafe/partial semantic dependencies and no exclusions.

The fourteen indices dispatch to the actual generated execute/ExecuteAs
program. Register-only paths frame the same fixed virtual save area while
SP changes. Memory paths require current SP=entrySP−16, prove their actual
addresses equal the fixed anchor, then invoke the completed native pair rule.
Initial saved words are arbitrary; stores update their actual payload and
loads update only the selected GPR. No return-value or saved-word equality
is assumed at entry.

The register branch restores literal frame/context/reservation resources.
The memory branch maps the genuine nested translation/A-D/data guards,
keeps observed CompletedFacts inside those branches, and returns all receipts
and the exact reservation update. The native Link supplies both register and
memory rules itself. No caller body-WP or success oracle occurs. The phase
SP contracts follow the exact scalar updates; full function phase/result,
fetch, clocks and restart remain separate composition obligations.

Evidence: owner build1,066 jobs; fresh audit
/tmp/xv6-lean-research/MycpuKptBodyRootAudit.lean and
/tmp/xv6-lean-research/mycpu-kpt-body-root-audit.log.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
