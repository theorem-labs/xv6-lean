# Initial proposal for a full Lean port of MachCSL/xv6iris

User: Jason Gross requests a full Lean port of arXiv:2609.04043 (Kaashoek and Zeldovich), hosted at theorem-labs/xv6-lean, with permission to fork/fix Lean Sail/RISC-V dependencies. This is the full machine-code theorem and all supporting proofs, not a toy ISA, standalone lock proof, or theorem assuming kernel correctness. I have read the complete 47-page paper. Current workspace is empty; no GitHub repo yet.

Proposed commitments:
- Preserve an exact, immutable upstream xv6iris snapshot and its kernel ELF, initial fs.img, Sail revision/configuration; derive byte-identical Lean data with reproducible tooling.
- Target Lean kernel checked proofs of concrete whole-system safety and pure filesystem consistency. Preserve arbitrary user code, sub-instruction interleaving, TSO, interrupt migration, DMA, out-of-order disk requests, and arbitrary repeated crash/reboot preserving durable disk. Explicit scope exclusions: liveness, noninterference, general RVWMO, hardware conformance beyond tested behaviors.
- Audit current Lean Sail backend before dependency decision: cannot use an interpreter whose monad hides memory/register events or collapses whole instructions into atomic transitions. Must expose a compatible event tree and prove bridge correctness, or extend/fork generator if necessary. Track reservations and atomic A/D update semantics.
- Reuse sound Lean Iris/OFE/CMRA/BI/invariant infrastructure if available; assess adequacy and universe/guarded recursion completeness. Otherwise port the needed Iris base, with an explicit milestone before kernel proof fanout. Do not replace Iris with Prop conjunction.
- Port operational semantics and top-level pure observations first. Keep explicit unfinished obligation inventory outside proved theorem namespace, no sorry/custom axioms silently accepted as completion.
- Prove logic adequacy before mass porting and complete one nontrivial closed end-to-end machine-code case with real Sail events and memory; use it to validate semantics, loader, CSL, and proof audit pipeline.
- Subsequent layers: TSO ownership/views/suspended views; device and power invariants; instruction specs and interrupt/translation capabilities; boot allocations; allocator/locks/context switching; VM/arbitrary user execution; processes/FD/pipes; buffer and inode caches; journal recovery and abstract filesystem; syscall linking and concrete image initialization; full adequacy and conformance.
- Separate Spec/Code/Proof/Link per function and named abstractions. Generated code is not hand edited. Keep authoritative contracts; changes require explicit cross-component review, never silently weaken contracts to unblock a proof.
- Agent management follows §7: small owned modules or independent worktrees, machine-checkable exit criteria, dependency-aware tasks, shared committed status and rejected-design notes, reviewers challenge ownership/concurrency/vacuity, fresh agents at checkpoints, axiom report and build-time measurements on every integration. No kernel changes merely to ease proof.
- CI pinned Lean and dependencies, build all imports, transitive axiom audit of exported theorem roots with explicit allowlist, theorem coverage/provenance report, and distinguish build success from full port completion.

Open design assessment needed: best practical sound Lean Iris base; whether direct port or checked translation of Rocq proof terms is viable without retaining Rocq as TCB; exact upstream pin; semantics generation bridge. No assumptions of feasibility yet. Research agents are independently auditing artifact and Sail.

Please critically review and contribute a concrete initial plan. Identify mathematical/engineering blockers, missing proof obligations, bad sequencing, risk of vacuity, and the strongest first executable milestone. Review the full paper available as /tmp/xv6-lean-research/paper.txt. Artifact clone may become available at /tmp/xv6-lean-research/xv6iris; inspect if present, otherwise report which recommendations await audit. Do not claim source inspection you did not perform. Do not modify files or post externally. Return review with decisive recommendations, not generic project management.


*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
