# Four-byte KPT memory: native implementation

FROZEN: all 21 approved contracts are implemented in 19 modules.
SupervisorMemOuter4 and SupervisorWriteEA4 each have five modules;
KptMemory4 has nine. `KptMemory4.nativeSpec` and `registrySpec` provide
both actual address and transformed-address WPs. Every native dependency
is supplied internally.

The public input is the actual original-tier KernelDatumWord4.word,
five auxiliary cells, native KptAddress residue, running context and
reservation. Addresses remain64 bits and payloads exactly32 bits.
Stores require full fraction and loads retain arbitrary fractions.
Four-alignment suffices, including address mod8=4 and page offset4092;
physical four-alignment and RAM/PMA/PMP bounds are derived from ownership.
No caller physical word, PPN, successful translation/read/write or WP
oracle appears. The explicit ambient controls remain exactly those of
KptMemory: actual supervisor/SXL, boot-PMA, HTIF-none, MPRV/MXR zero,
PMM disabled and ADUE one.

The actual raw vmem paths retain exception callbacks and offset addresses,
all eager effective-privilege/PMA/PMP reads, false store responses and
all32 payload bits. Write-EA performs its permission reads and the actual
pure announcement; the ordinary data write is the separate real event.
Native rules return the source tier/context word, all control resources,
the coherent post-translation residue and every translation receipt.
The original hit/miss/A-D guards are preserved, with one additional data
later/view. Loads retain the translation reservation; stores clear it.
Transform, address and completion proofs reuse width-independent native
translation facts without changing existing families.

Final build: 1,054 jobs, no warnings. Strict owner audit: all255 physical
declarations across19 modules, including private helpers, full types,
opaque bodies and constructors; only propext/Classical.choice/Quot.sound,
zero exclusions, unsafe/partial logical dependencies or Initial calls.
Twenty-four kernel edge fixtures passed, including four-not-eight
alignment, page/RAM-end limits, nonidentity PPN offsets, full32-bit
payloads, request size/plain flags, raw false/error tails, no-event EA,
actual vmem programs and reservation behavior.

Evidence under `/tmp/xv6-lean-research/`: `kpt-memory4-build.log`,
`KptMemory4OwnerAudit.lean`, `kpt-memory4-owner-audit.log`,
`KptMemory4Checks.lean`, `kpt-memory4-checks.log`, and
`kpt-memory4-freeze.json`. Source correspondence and dependency details:
`docs/design/kpt-memory4-boundary.md`. Independent implementation review
is assigned to the coordinator after this frozen handoff.

No new camera, allocator, generated model change or old-family edit.
Actual load/store instruction decoding, sign extension, cycle, interrupt
resources, full push_off and source boot inhabitation remain later
consumers. The present rule operates on an already computed effective
virtual address and its actual supplied native datum resources.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
