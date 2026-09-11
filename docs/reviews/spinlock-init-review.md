# Independent review of spinlock boot-resource assembly

Reviewer: OpenAI Codex subagent `lean_logic_audit`, independently reviewing
coordinator-authored `MachCSL/Logic/SpinlockInitProofs.lean`.

Result: **PASS after a syntax correction**. The reviewer found the documentation
comment before `omit [Platform] in`, which Lean rejects. The coordinator moved
`omit` before the comment; the final file rebuilds successfully (536 jobs).
No ownership or theorem-contract correction was required.

`allocate` consumes the actual TSO `bootClients` for an explicit finite memory
map whose decoding equals the memory of an actual `BootFacts` witness. The
existing extraction provides seventeen exact instruction windows and the two
zero-valued writable data windows, with disjoint selected keys. Both residual
full byte/timestamp maps and the original length-zero receipt survive.

Only the code timestamps are converted to persistent pristine facts, and its
full byte ownership is split into eight positive one-eighth shares. The lock
and counter retain their full byte/timestamp ownership and are deposited into
the freshly allocated native lock invariant. Each idle protocol resource
contains only persistent scenery, so universal distribution over all harts
does not duplicate the counter or holder fragment. Capacity/name unfolding
connects the same existing heap, TSO, metadata and lock resources; there is no
replacement authority or new native invariant world.

The conclusion is resource initialization. It does not assert register
initialization, a complete boot handler, all-pool operational exclusion or a
closed two-hart theorem. The conditional map-decoding premise is explicit and
is discharged separately when connecting actual era allocation.

A fresh physical-origin audit checked all 3 declarations in the file, including
private declarations and full type/body/constructor dependency cones. Only
`propext`, `Classical.choice` and `Quot.sound` occur; no unsafe/partial dependency
or excluded runtime companion was found. Evidence:
`/tmp/xv6-lean-research/SpinlockInitPeerAudit.lean` and
`/tmp/xv6-lean-research/spinlock-init-peer-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
