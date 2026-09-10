# ELF port status

`Defs.lean` follows the records, readers, table order, PT_LOAD filtering and
structural checks of `iris/ElfFile.v` at the pinned paper commit. Full-width
unsigned fields are represented by nonnegative `Int` values, preserving the
reference's arithmetic and negative-offset rejection. Zero-width reads retain
the reference behavior: they succeed at any nonnegative offset.

The underlying representation is partial packed-page lookup. Unlike the
reference's contiguous byte list, a user-constructed packed image may have
missing pages; a read through one is rejected. A coverage/lookup theorem relating
valid packed images to reference lists is still required. The current source
transcription is therefore not a completed representation-correspondence proof.

General proofs cover negative/empty reads, successful table length, the program
header validity predicate, and disjoint loaded ranges. `Kernel.lean` uses ordinary
kernel-checked `decide` proofs for the exact paper ELF header, its load-segment
geometry, loadability and section-table bounds. An empty input is proved invalid.
These facts depend on the generated packed constants, not independent replacement
header literals. The expected literals are checked conclusions.

Not implemented: loaded file/zero maps, the generated kernel instruction/data
map correspondence, the rest of the general ElfFile proof library, filesystem
ELF loading, and machine boot initialization. Structural loadability is not a
kernel execution or filesystem safety theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
