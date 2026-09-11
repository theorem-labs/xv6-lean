# Independent review: native barrier rules

Verdict: PASS. Codex root independently read all four BarrierWP modules and the
complete pinned HartBarrier.v. The direct-node scope is explicit: the source
mctx/swp abstraction is still a separate obligation.

The actual barrier step and uniqueness proofs retain every machine field except
the selected view. All kinds use the source fencePost classifier. The draining
interface exposes ownPub ≤ view and a native receipt, never a global-log-top
bound. The general interface exposes neither fact. Its heap/TSO basic update
restores the same state; the proof frames the other five era conjuncts, durable
disk, fixed resources and observation interpretation. Native WP handles live
and stale generations and pays its actual silent step; the private update
factor is fully discharged by the public proofs. The concrete link reuses the
allocated invariant world and introduces no new camera.

A fresh 431-job build passed. The separate physical-origin audit checks all 52
declarations, including private helpers and full type/body dependencies: only
propext, Classical.choice and Quot.sound; no unsafe/partial dependencies or
runtime exclusions. Commands used tools/lake.py build MachCSL.Logic.BarrierWPLink
and env lean /tmp/xv6-lean-research/BarrierWPRootAudit.lean.

These results establish the generic barrier leaf, not the two-hart lock theorem
or any application-specific publication protocol.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
