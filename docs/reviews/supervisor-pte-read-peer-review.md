# Supervisor PTE read independent review

Reviewer: Codex subagent `lean_logic_audit`, independently reviewing the
coordinator's frozen SupervisorPteRead Defs/Spec/Plan/Proofs/Link and
STATUS. **PASS** for the declared direct physical-wrapper boundary; no
code correction requested.

I read all five modules, their design and STATUS, the actual generated
`Vmem.read_pte`/`read_pte_exclusive`, `Mem.checked_mem_read`, the explicit-
privilege wrapper and metadata drop, and `PhysMemInterface.read_ram`.
Source comparison covered `PtTreeAdue.v:854–891,1612–1653` and
`HartSKpt.v:609–650` at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. I also inspected the supporting
native TsoPinnedReadWP pure assembly, power restoration and event proofs.

The definitions retain `Load PageTableEntry`, PBMT_PMA, explicit Supervisor,
eight bytes, both actual reservation flags and normal-strength plain or
exclusive requests. Config requires the actual PMA `supports_pte_read`
grant, aligned RAM range, matching PMA entry, TOR configuration and disabled
HTIF. The existing TOR record requires full RWX, which the STATUS explicitly
states; this is not advertised as the source's minimal read-only PMP
hypothesis. The four fractional cells cover exactly five register reads,
including the repeated PMP configuration read. No status/privilege read,
write-EA event, fixed whole-register snapshot or software callback is added.

The finite prefix is a proof about the actual generated program. It
retains PMA priority, split handling, PMP, eager MMIO tests, read-kind
selection and singleton assembly. `OneRead.bind` preserves the raw error
Exit residual through the real empty-result error event, without inserting
a successful result. Every successful tag is accepted and dropped exactly
as generated. `program_eq` and the two entry equalities preserve the outer
callbacks and metadata drop. Public WPs construct this prefix internally;
the caller does not supply a successful read or a Boundary witness.

The ordinary native fold accepts every allowed view and derived word.
Its owned physical-value function is independent of the canonical PTE
reference, and its conclusion is canonical equality plus exact equality
when that reference is an interior entry. The underlying assembly uses one
common view for every byte. Publication credentials, pin anchors, register
cells and the original reservation are all framed and returned.

The exclusive native fold derives current physical readback from heap
ownership, installs the actual snapshot and returns the original full
slot with its floor/timestamp/allowed-set/anchor components. It requires no
publication credential. The physical projection is used for a pure query,
not to duplicate a fractional byte resource. Native blocked rereads clear
the local reservation and retry; successful rereads install the snapshot
and top-view receipt. These behaviors remain those of the actual event
rule, and no disjointness or fairness premise is introduced.

The two public contracts have a proved native inhabitant using the same
capacity and Iris world. The final caller WP is only the genuine program
continuation. These rules own a slot directly: shared KPT opening/closing,
canonical tree ownership, TLB consistency, leaf validation and the complete
Sv39 hardware walk remain separate. No complete source mycpu or model-to-
Rocq correspondence result follows from this checkpoint.

Independent validation rebuilt the Link target successfully (**621 jobs**).
A fresh physical-origin audit checked **79 declarations** across all five
modules, including private helpers and all transitive types, opaque proof
bodies (`allowOpaque := true`) and datatype constructors. Only `propext`,
`Classical.choice` and `Quot.sound` occur; no unsafe/partial logical
dependency and **zero excluded compiler companions**. Evidence:
`/tmp/xv6-lean-research/SupervisorPteReadPeerAudit.lean`,
`supervisor-pte-read-peer-audit.log`, and `supervisor-pte-read-peer-build.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
