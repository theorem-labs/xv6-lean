# Independent supervisor physical-fetch review

Codex coordinator read all five SupervisorFetchRead modules and the generated
checked_mem_read and read_ram definitions. PASS. Width two and width four have
separate checked proofs with exactly their own alignment premise. The PMA/PMP
and HTIF checks pay five actual reads from four independently fractional cells.
The emitted request is the generated plain normal V1 read, including its exact
metadata, and the proof retains all successful tag responses and the error Exit
tail. Full-width data assembly is proved for arbitrary 16/32-bit words.
The native fold derives actual read access from the context byte window, frames
registers and reservations, and returns the actual chosen-view receipt.

Fresh independent `tools/lake.py env lean /tmp/xv6-lean-research/SupervisorFetchReadAudit.lean`
passed all 89 declarations by physical origin, traversing types, opaque bodies
and constructors, with the standard three axioms, zero exclusions and no
unsafe/partial logical dependencies. This is checked physical fetch access;
outer effective privilege, virtual translation and full instruction-fetch cycle
composition remain explicit dependencies.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
