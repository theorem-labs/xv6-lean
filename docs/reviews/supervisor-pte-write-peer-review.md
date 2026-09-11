# Independent supervisor PTE write review

Reviewed all five frozen modules against the actual generated Vmem conditional
wrapper, Mem PMA/checked-write/value layers and PhysMemInterface write_ram.
The native Spec is inhabited by the actual program. Store PageTableEntry,
conditional=true, PMA supports_pte_write and all Boolean/error callbacks are
preserved. The complete PMP-tree equality permits only the justified PMP reuse;
it does not replace PMA or the final event with an ordinary Data store.

The register plan retains the four fractional cells and five actual reads.
The native fold preserves those cells, pays the real memory event with full
pinned resources and a held snapshot, and returns authored history, positive
time, updated pins, view and cleared own reservation. The blocked branch keeps
its original state and resources. The exact result true follows from the actual
successful raw response, without a success or reservation-separation oracle.

A fresh independent physical-origin audit checked all 177 logical declarations,
private helpers, transitive types, opaque bodies and constructors: only propext,
Classical.choice and Quot.sound; zero exclusions or unsafe/partial dependencies.
Evidence: SupervisorPteWritePeerAudit.lean and
supervisor-pte-write-peer-audit.log under /tmp/xv6-lean-research.

PASS for this direct physical wrapper. Shared KPT access, exclusive reread/update
composition, Sv39 translation and the whole-kernel roots remain separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
