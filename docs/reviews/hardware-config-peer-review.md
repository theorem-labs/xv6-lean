# Hardware configuration: final independent native review

PASS for the declared native component. Codex subagent artifact_audit read all
four frozen coordinator-authored Xv6/Kernel/HardwareConfig{Defs,Spec,Proofs,Link}
modules, full design and STATUS, following the earlier independent signature
review. Rechecked source RiscvFetchExec.v275–338 and the separately reviewed
PmaClass source/generated-model boundary. No source code change was requested.

Every public constructor retains exactly the six frozen hardware cells,
two existential counter cells, eleven hardware facts, static mapping claims
and actual generation certificate. All eight owned fragments are persisted
individually through the real native register rule. mcounteren remains absent;
its lifetime belongs to TimerCap. boot is a pure fact about explicit values,
not allocation of those resources or reachability of a configured hart.

The performance factorization is sound: private bundle abstracts only the
large static-claim assertion. Each public actual Spec field instantiates P
with precisely KernelMapStatic.claims capacity era.kernelMap. No public rule
receives a caller-selected assertion, equivalence, restoration callback or
preservation theorem. The resulting bundle is definitionally config. Generic
access requires native Persistent P; its actual instantiation is discharged
by the existing static-claim instance. The map accessor specializes the same
P before applying the actual native static-map lookup law. No alias replaces
full map claims with a tokenless predicate or an empty allocation.

The remaining resource laws use actual native persistence and typed GhostMap
agreement. The counter accessor returns the original arbitrary existential
values. The MISA/PMA accessor requires a real separately owned matching cell.
The generation certificate's persistence comes from StateInterpProofs and
is not assumed. All nine native fields and all three pure fields are closed.

Independent build passed667 jobs. A fresh audit checked every68 physical
declaration in the four modules, including all private generic helpers,
with exporting disabled, collectAxioms and full type/opaque-body/constructor
traversal. Only propext/Classical.choice/Quot.sound; no unsafe/partial
semantic dependency; zero exclusions. Evidence is
/tmp/xv6-lean-research/HardwareConfigPeerAudit.lean and
hardware-config-peer-{build,audit}.log.

PMA scope remains explicit: config allows arbitrary tables satisfying the
native address-class property. It does not pin regions to pmaBoot. The
source Int atomic-width versus generated Nat-domain correspondence caveat
is documented in the PmaClass peer review. Current KptAddress/Memory/Fetch
execution contracts requiring pmaBoot are strictly more specialized than
this configuration; those equalities cannot be inferred from config alone.
No full source capability, boot inhabitation or whole function WP is claimed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
