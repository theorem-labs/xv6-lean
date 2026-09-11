# Independent shared page-table ghost review

PASS for all five KptGhost modules. The coordinator read the complete
Defs/Spec/Proofs/Registry/Link and compared the interface with the source
KMap/KptGhost representation already reviewed in the shared-KPT design.
The native map uses discarded persistent fragments; tree and bound use
separate exact Csum/Excl/Agree one-shot cameras. Snapshot equality is only
canonical tree equality. Bound includes the caller's actual log-length
lower bound, including the existing zero-bound definition.

All eighteen contracts have native proofs. Map allocation persists each
fragment actually returned by the native allocator. Fresh insertion proves
the existing ExtTreeMap/PartialMap insert correspondence and returns both
authority and claim under the same basic update. This explicit grouping
corrects the notation-scoping error caught during implementation. Pending
exclusivity, shot agreement and frame preservation follow from the actual
cameras. No fresh physical truth is inferred. Bound validity additionally
requires authority for the same supplied log name and capacity.

The registry adds exactly slots45–47 after SupervisorBits44, and its generic
preserveOld theorem transports every earlier element witness. The named
machine, byte, TSO, filesystem, crash, UART, invariant and supervisor capacities
retain their old indices. The KPT view and log counters are definitionally
the same machine slots2/3; invariant slots16–19 are retained. Link checks
all four existing era-name projections and closes the native specification.

The owner build passed 600 jobs. The full physical-origin audit covers all
353 declarations in five modules, following types, opaque bodies and
constructors; only the standard three axioms occur, with zero exclusions
and no unsafe/partial semantic dependencies. The coordinator independently
reran that audit successfully; evidence is
/tmp/xv6-lean-research/KptGhostOwnerAudit.lean and kpt-ghost-root-audit.log.

This layer allocates ghost state only. Physical tree ownership, map validity,
shared invariant allocation and actual boot publication remain separate.
The review used distinct implementation and review AI-agent roles; it is
not a human review.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
