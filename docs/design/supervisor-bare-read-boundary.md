# Actual Bare virtual read composition

Root owns SupervisorBareRead{Defs,Spec,Plan,Proofs,Link}+STATUS. Prove actual
vmem_read_addr (.Virtaddr address) 8 (.Load .Data) false false false from one
seven-cell fractional footprint, exact generated address checks/page split,
translation mode and translateAddr, outer effective privilege and checked
physical read. Reuse the reviewed BareFetch footprint; it owns status,
privilege and satp only once across repeated reads. Pure prefix gives fifteen
actual reads before one real normal read event, then exact full-word assembly.

Explicit configuration is Supervisor/SXL2/Bare/MPRV-clear, exact matching
readable PMA/TOR RAM and disabled HTIF. Public native WP derives alignment
from actual context-word ownership. The page-split proof is shared with the
parallel BareWrite proof; no independent page model or unchecked assertion.
Boundary proofs preserve all actual successful/tag and error-Exit tails;
no memory_exception or arbitrary result is removed by hypothesis. Native
rule internally derives all-view readability and returns same7cells/context/
word and chosen-view receipt through the actual guarded continuation.

No base register or effective-address pointer transformation is covered here;
vmem_read, fetched LOAD, source stack and KPT mappings remain subsequent work.
This explicit Bare tier is not source full supervisor function correctness.
No new camera or semantic oracle is introduced.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
