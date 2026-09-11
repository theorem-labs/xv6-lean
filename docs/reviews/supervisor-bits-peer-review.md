# Native supervisor bit ownership review

Verdict: PASS for the five-module resource component. Coordinator read all
Defs/Spec/Proofs/Registry/Link, design, and source IntrDefs196–207,309–452,
649–678,932–936 plus the exact nominal-MPP helper. All twelve contracts are
constructed by actual/nativeSpec; no WP or architecture-success premise is
introduced.

The live tie owns the actual full mstatus cell, its SIE half, two SRET mirror
halves and all ten source status facts. The two eighths and handler quarter
are retained under fresh attachment. Allocation returns existential fresh
names and preserves the existing physical register; canonical Era wrappers
only refer to existing tokens. Both full-fraction flips preserve every piece;
SRET updates gather both halves of both names. Count/arm agreement uses the
source eighth, with the depth-zero saved bit and positive-depth zero bit.

Slot44 is the actual GhostVar BitVec1 functor. Registry proofs preserve
slots0–43 and45+, transport every prior FsCrash capacity and equate physical
register capacity with MachineInterp. No name fields, CSR writes, handler
installation, migration rule or full sconf/capability are claimed by this
component. A ghost flip alone is not execution of a machine instruction.

Owner build passed578 jobs. Coordinator reran the complete physical-origin
234-declaration audit including private/generated roots, transitive types,
opaque bodies and all datatype constructors: standard three foundational
axioms only, zero exclusions and no unsafe/partial dependencies. Evidence:
/tmp/xv6-lean-research/SupervisorBitsAudit.lean and
supervisor-bits-root-audit.log. No correction requested.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
