# Independent mycpu cycle-shell review

Result: PASS for the four frozen `Xv6.Kernel.MycpuCycleShell` modules.
No production changes requested. This review was performed independently
by the OpenAI Codex sail_audit agent; the coordinator owns the implementation.

Read all Defs/Spec/Proofs/Link, the actual `Machine.Node.cycle`/restart
relation, generated `Step.try_step` and `Platform.tick_clock`, the exact
SupervisorRetirement factor and native completion rule, common footprint
membership/uniqueness, MycpuActive.Prefix.fold, and RestartWP's actual
machine-step/successor and native reservation-update proof. Pinned source
comparison includes `RiscvLang.v:222–225` and
`RiscvExec.v:1007–1024`. The checked factor theorem is equality of complete
free event trees, not an equality only of terminal register files.

The source cycle discards try_step's Bool result and conditionally invokes
the clock; the factor retains both waiting and active branches before
routing every Step outcome through the unchanged postlude. The active
prefix requires the actual hart-state premise, runs the real setup
(including its privilege/counter-filter reads and flag write), then reads
hart_state. It derives preservation of that cell through setup before
selecting the active branch. The resulting active-body WP remains an
explicit linear continuation; neither instruction execution nor fetching
is assumed completed by this theorem.

The common footprint has 28 unique register keys. Its existing membership
proofs provide the exact setup/retirement cells, full PC/nextPC and the
three full writable clock cells. Readable configuration fields retain their
caller shares. Clock readAny branches remain in the underlying actual
execution plan, so no unowned configuration read is replaced by a chosen
value. The symbolic `completed` relation constrains nonclock fields and
makes no claim that an unowned physical register stayed unchanged.

The successful suffix specializes the exact source Retire_Success arm,
requires active hart state to justify its assertion, advances PC from
nextPC and handles minstret according to its actual flag. Both tick values
flow through the existing checked clock plan and preserve the complete
common footprint. The shell does not conflate success-only suffix rules
with a proof that the unresolved active body necessarily succeeds.

The restart composition invokes the genuine machine transition from a
pure hart computation. It consumes the caller's actual reservation fragment,
uses native authority update to clear it, and supplies a fragment at none.
The arbitrary original reservation and every nextTick Bool are retained
in the source contract. The continuation's later guard is discharged at
that real restart transition; it is not erased by monadic simplification
or a pure recursive equation. Register cells survive in the guarded
continuation, and the generation certificate is persistent. Existing
RestartWP accounts for both live and dead-generation successors and
preserves the full machine/observation interpretation under its native
mask protocol. The shell introduces no extra mask assumption or ghost
allocation.

Validation: the owner reports the final four-module build passed 662 jobs.
This review independently ran the four-physical-origin audit via
`tools/lake.py env lean /tmp/xv6-lean-research/MycpuCycleShellOwnerAudit.lean`;
`/tmp/xv6-lean-research/mycpu-cycle-shell-peer-audit.log` reports all 34
logical declarations passed. It traverses private/generated roots, all
opaque bodies, types and datatype constructors. Only `propext`,
`Classical.choice`, and `Quot.sound` occur, with zero excluded roots and no
unsafe/partial or `FsDurSnapshot.Initial` dependency. No competing build or
production edit was performed. The final MycpuCycleShellSTATUS.md was also
read: its 662-job build, 34-declaration audit and explicit residual active-body
obligation agree with the reviewed code and this limited approval.

Frozen SHA256 values:

| File | SHA256 |
| --- | --- |
| Defs | `42b5812469e6a6ed9c73f24d96ff71a27218c329772e8a79357d1442c504d68d` |
| Spec | `7f1634d86621a6a5935af500863bb080b57eeed22909829e0f46311737fff8d0` |
| Proofs | `3919bfb07d6fb4b46423ea606d4edbe87a76fe66fcff364239b7c1e7185f6fb1` |
| Link | `8668e5996027731d96512309367100a1428d325e3bcc23f1c7ce2c925044ba4a` |

This approval covers the cycle shell and exact successful suffix/restart
composition. It does not approve a closed active instruction WP, complete
fetched cycle, whole mycpu function or whole-system adequacy from these
modules alone.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
