# PMA address classes: independent source and implementation review

PASS for the native generated-model contracts, with the signed-width scope
qualification below. Codex subagent artifact_audit independently read all
three frozen coordinator-authored MachCSL/Machine/PmaClass{Defs,Spec,Proofs}
modules and STATUS. Compared pinned RiscvFetchExec.v75–175 and RiscvExtras
pma_ram_access/pma_io_access with actual generated Pma matching/override/
atomic definitions and the transparent Platform boot regions. No source
implementation correction was requested.

The range predicates retain positive bounded widths and both address/end
bounds, so they exclude wrapping or out-of-region accesses. The proofs
establish actual first-match lookup in the complete boot table, including
failure of preceding ROM/IO regions for RAM. Matching uses actual generated
range_subset and the 64-bit width conversion. The attributes keep execution,
read/write, every generated AMO through16, PTE read/write, misaligned plain
access permission and reservability; IO retains only its two source fields.
No synthetic lookup result or memory-success assumption is used. Seven
actual Spec fields are all discharged by native proofs.

The source outer matching width is Int but constrained1≤n≤4096, whereas the
actual generated Lean function uses Nat. These admitted domains align.
Separately, the source inner atomic conjunct quantifies *all* Int n≤16,
including negative values; the Lean grants conjunct quantifies Nat widths
(including0). The outer positivity bound does not by itself justify this
inner restriction. The current proofs cover every actual generated Nat
request, but do not establish a formal equivalence to that full signed
source predicate. This qualification was explicitly sent to the coordinator;
it is not a generated-machine safety defect or an execution-oracle premise.

Independent build passed106 jobs. Fresh strict audit covered every96
physical declaration across all3 modules, including generated/private roots,
with exporting disabled and complete type/opaque-body/constructor traversal.
Only propext/Classical.choice/Quot.sound occur; no unsafe/partial dependency,
zero exclusions. Evidence: /tmp/xv6-lean-research/PmaClassPeerAudit.lean and
pma-class-peer-{build,audit}.log. This proves a pure PMA table property, not
allocation, startup reachability or cross-prover semantic correspondence.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
