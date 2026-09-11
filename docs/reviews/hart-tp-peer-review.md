# Native HartTp ownership review

Verdict: PASS for all five modules. Coordinator read Defs/Spec/Pure/Proofs/Link,
source HartTp45–137 and WpGpr95–138, and the twelve pure/nine resource contracts.
The software file is total on32 five-bit indices, with an explicit typed
x1–x31 mapping and hardwired x0 fact. All32 generated rX_bits forms are checked
by kernel reflexivity. Enumeration completeness, physical uniqueness and31-cell
count are proved; constructor arithmetic is not used.

Lookup splits the actual whole file by a checked permutation and the exact
filtered remainder. Replacement updates only the selected entry and retains
all other cells. x0 replacement still requires its zero fact. Pin/update
commutation excludes TP; the full actual x4 accessor carries hartWord cpu.
Actual physical TP agreement uses the existing native register authority rule,
which the final Link discharges. No persistent TP ghost, migration rule or
full function adapter is asserted.

Owner build passed349 jobs. Coordinator reran the full physical-origin155-root
audit with types, opaque bodies and datatype constructors: only the standard
three foundational axioms, no exclusions or unsafe/partial dependencies.
Evidence: /tmp/xv6-lean-research/HartTpAudit.lean and hart-tp-root-audit.log.
The source gmap/domain encoding is represented by the checked complete finite
list; its domain fact is a proved pure tautology, not an additional resource.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
