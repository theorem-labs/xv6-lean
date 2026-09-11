# Native mycpu cycle independent review

PASS for the four actual cycle-and-restart contracts. Root reviewed the
complete Defs/Spec/Proofs/Link, design and STATUS, alongside the previously
reviewed Entry and Shell factors and native restart rule.

Every public rule consumes the actual 28-cell bundle and original-rs
configuration. `started_*` transports the exact required fields through
setup's sole minstret_increment write. Entry proves the current fetch and
body; native finish/restart proves actual retirement, both current clock
choices and both next-tick choices. The final Completed relation fixes all
off-clock cells relative to actual completeAfter. Each family separately
proves the hart remains active before using the postlude.

The real reservation is retained through scalar/load/return until restart,
then cleared; store passes its already-cleared fragment. Context, shared
boot text, stack word/fraction and independent view receipts are framed
exactly. Two guards for scalar/return and three for memory are paid by the
actual fetch/data/restart steps. The callback proves only the next cycle;
there is no assumed current body or preservation theorem. The actual target
is Machine.cycle, with all source waiting/error branches retained in its
factors. This does not yet prove fourteen-cycle function chaining or KPT.

Fresh root audit `MycpuCyclePeerAudit.lean` passed all **63 logical
declarations** in four physical modules, including private helpers and
complete transitive types, opaque bodies and datatype constructors. Only
the standard three axioms occur, zero exclusions, no unsafe/partial cone.
Evidence: `/tmp/xv6-lean-research/mycpu-cycle-peer-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
