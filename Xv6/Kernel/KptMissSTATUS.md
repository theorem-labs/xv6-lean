# Shared KPT miss: frozen

All seven KptMiss modules compile successfully (832 jobs). Link constructs
four pure contracts and one native miss contract using actual KptTreeWalk
and KptAD implementations. The coordinator approved Defs/Spec before proofs;
the five signatures remain unchanged.

Fresh full physical-origin audit checks all 89 declarations (including
private/generated helpers), types, opaque bodies and datatype constructors.
Only propext/Classical.choice/Quot.sound occur, zero exclusions, no unsafe/
partial semantic dependency and no Initial dependency. Seven additional
kernel selection/raw-global branch checks pass.

The actual miss composes raw-upper shared walk, observed-word shared A/D
branches and real TLB fill. Six control cells, persistent shared/snapshot/
bound/credential clients, all three walk receipts, exact branch reservation
and A/D receipt are explicit. BranchFacts remains inside 0/0/1/2 A/D guards
after the three walk guards. Final snapshot-relative coherence is derived from
canonical equality, separately proved stable PPN/G and the actual fill. No initial physical word or direct slot is input; no
G=false/flag-one upper restriction is inherited from Sv39Miss.

Source mapping: docs/design/kpt-miss-boundary.md. Validation evidence:

- /tmp/xv6-lean-research/kpt-miss-build.log
- /tmp/xv6-lean-research/KptMissOwnerAudit.lean and kpt-miss-owner-audit.log
- /tmp/xv6-lean-research/KptMissChecks.lean and kpt-miss-checks.log
- Initial signature check: kpt-miss-signatures.log

Existing frozen modules and umbrellas are unchanged; no camera or allocation
is introduced. This proves the full shared miss under the stated source
clients/hardware conditions, not complete lookup/translation dispatch or
translated mycpu from boot.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
