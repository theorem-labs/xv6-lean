# ELF port status

`Defs.lean` follows the records, readers, table order, PT_LOAD filtering and
structural checks of `iris/ElfFile.v` at the pinned paper commit. Full-width
unsigned fields are represented by nonnegative `Int` values, preserving the
reference's arithmetic and negative-offset rejection. Zero-width reads retain
the reference behavior: they succeed at any nonnegative offset.

The underlying representation is partial packed-page lookup. Unlike the
reference's contiguous byte list, a user-constructed packed image may have
missing pages; a read through one is rejected. `Image/PackedProofs.lean` now proves coverage/lookup and bounded-read
correspondence with contiguous lists. `Image/Coverage.lean` proves coverage for
both actual inputs. `Representation.lean` proves the complete ELF reader
correspondence, including negative, zero-width and truncated reads, and relates
the natural and integer little-endian folds. Correspondence with the raw hex
encoding and generated Sail byte routines remains separate.

General proofs cover negative/empty reads, successful table length, the program
header validity predicate, and disjoint loaded ranges. `Kernel.lean` uses ordinary
kernel-checked `decide` proofs for the exact paper ELF header, its load-segment
geometry, loadability and section-table bounds. An empty input is proved invalid.
These facts depend on the generated packed constants, not independent replacement
header literals. The expected literals are checked conclusions.

`Image.lean` defines pointwise file-backed, zero and combined maps with the
reference's truncated windows and left-biased segment union. It proves generic
range and BSS properties; `ImageFacts.lean` proves zero values throughout the
actual kernel's BSS. `ImageRepresentation.lean` proves pointwise-map/list-map
correspondence; `ParserRepresentation.lean` extends this through complete header,
table and image parsing under coverage. Generated kernel instruction/data map
correspondence, the rest of ElfFile's proof library,
filesystem ELF loading and machine boot initialization remain unimplemented. Structural loadability is not a
kernel execution or filesystem safety theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
