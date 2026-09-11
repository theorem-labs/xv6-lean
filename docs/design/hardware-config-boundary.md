# Exact persistent hardware configuration

Source RiscvFetchExec.v281–333 at the paper pin defines six frozen hardware
cells and two counter-permission cells. This component preserves exactly
misa, mseccfg, pma_regions, HTIF-none, elp, senvcfg-zero, scounteren and the
mhpmcounter vector. It never freezes mcounteren, which timerinit writes.
All eleven source facts are present, including literal MISA/mseccfg and the
complete address-class PMA obligation, with static map claims and the real
generation certificate at the same era names.

Three pure contracts establish the concrete literal/PMA fact bundle and its
projections. Nine native contracts establish persistence, actual eight-cell
persistence and construction, complete access, counters, same-cell agreement
and exact static map lookup. Source conjunctions and existentials are regrouped
into a typed Values record; no additional actual register is owned by that record.

The proof uses a private generic framing assertion to avoid proofmode eagerly
normalizing the49,154-entry static map during introduction. Every public rule
instantiates that parameter with KernelMapStatic.claims at era.kernelMap.
No arbitrary predicate or update callback is a premise of the public native
constructor. The resulting resource body is definitionally the declared config.
All eight register fragments are individually persisted using the native rule.

The input cells, static claims and certificate must already be owned. The
constructor does not allocate them, install an era or prove boot reachability.
The PmaClass design records the precise Nat-width backend scope and signed
atomic-width correspondence limit. No full cross-prover equivalence is claimed.

Independent signature review passed before implementation. Native Proofs
build passed666 jobs; final Link and strict physical audit are recorded in
HardwareConfigSTATUS.md. No new camera, axiom or frozen dependency change.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
