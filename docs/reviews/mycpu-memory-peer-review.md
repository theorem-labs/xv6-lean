# Independent mycpu memory-body review

Read all five modules against `ProofMycpu.v:99–136,212–248`,
`WpSconfMem.v:3656–3741`, and the actual generated execute/virtual-memory
bodies through their kernel-checked equalities. The two stores target
SP+8 with RA and SP with S0; the two loads reverse those transfers.
STORE reads its data register before SP. The exact dependent full-word
slice is justified by a typed equality, without a semantic substitute.

The one ten-cell footprint retains arbitrary configuration fractions and
fractional SP; loads require full target ownership. The real virtual-memory
boundary is widened and folded at that footprint, with no duplicated
configuration cells. All response tails are retained: STORE ignores its
returned Boolean and retires on either Boolean; LOAD keeps the target
write and actual error Exit. Native RAM/context ownership discharges
successful accesses and blocked-store retry, deriving alignment from the
owned word. Native loads retain reservations; successful stores clear them.

The public rules expose actual Bare/permission/zero-mask configuration
and native word/context resources. Source KPT tier, SIE capabilities,
fetch/retirement/migration and full-function correctness remain open;
these are explicitly scoped prerequisites. Pure after-state and modular
save-slot lemmas match the instruction bodies.

Fresh independent audit passed all 135 declarations across all five
physical modules, including private helpers, transitive opaque bodies,
types and constructor dependencies. Only propext, Classical.choice and
Quot.sound occur; zero runtime exclusions and no unsafe/partial dependencies.
Command: `PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py env lean
/tmp/xv6-lean-research/MycpuMemoryAudit.lean`.
Evidence: `/tmp/xv6-lean-research/mycpu-memory-peer-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
