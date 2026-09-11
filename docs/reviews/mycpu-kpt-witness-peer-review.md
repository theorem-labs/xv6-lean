# Independent configured Sv39 witness review

Verdict: PASS for the sixteen closed configured-witness contracts. The
coordinator read all ten final modules and ran a fresh full audit with
exporting disabled. It checked all 222 physical declarations, including
private declarations, full opaque values, types and constructor dependencies.
Only propext, Classical.choice and Quot.sound occur; no unsafe/partial
dependency and zero exclusions. The proof-only evaluator is noncomputable,
so the initial unnecessary runtime recursion companion has been eliminated.

All fourteen certificates normalize the actual generated cycle. The flat
register helper is proved equal to the original complete checkpoints first;
it does not weaken the equality or remove TLB or counter checks. Every cycle
checks all 180 registers and every local state field. The generic evaluator
soundness theorem converts the checked equations into actual NodeSteps.

The concrete image includes all 512 entries of each of three page-table
pages. Its code and stack translations use the actual Sv39 walk/fill paths;
A/D bits are preset. The result restores the callee-saved registers, SP and
RA, returns the correct CPU address, retains Sv39 SATP and the two actual TLB
entries, and records exactly two stack stores and fourteen retired cycles.
Code, page tables, other memory and global state retain their stated frames.
The positive execution lifts to the real twelve-thread pool with the other
harts and device workers present. Initial/final memory and reservation
invariants are proved.

This is a configured image witness, not boot reachability, native Iris entry
resource allocation, a universally quantified function WP, or the source's
complete supervisor capability. Those limits remain explicit.

Build: 738 jobs. Independent evidence:
`/tmp/xv6-lean-research/MycpuKptWitnessRootAudit.lean` and
`/tmp/xv6-lean-research/mycpu-kpt-witness-root-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
