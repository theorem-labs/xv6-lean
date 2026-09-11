# Independent review: directory reader and first-match map

Reviewer: Codex coordinator. Read both Lean modules and their source definitions
and central laws in `DirentEnc.v`, `DirView.v`, `FsTree.v` and `InodeDefs.v`.

Names remain raw byte lists, with the first NUL and fourteen-byte cap governing
canonical equality. Free entries may contain arbitrary name garbage. The
sixteen-byte record reader uses the same block/offset division and little-endian
halfword assembly as the source, including crossing into the next block.

The ascending first-index scan is identical to source `dfirst`. Its Some and
None characterizations prove bounds, matching and absence of earlier matches.
The map first filters winning records, then performs the source ordered,
first-winner list-to-map conversion. The lookup theorem relates this exact map
to the actual first record without assuming uniqueness or padded names.
Uniqueness is required only for the later arbitrary-live-record value theorem.

The unsigned inode and link-count guards and index-pinned dot predicate match
their source conditions. Kernel regression proofs cover duplicate canonical
names, NUL truncation, free-entry garbage and the record64 block boundary.
The implemented encoding bridges cover the first record; full block encoding,
updates and the remaining name-comparison laws are explicitly still pending.

Review: PASS for this foundation. Directory W6–W8, W9 and complete filesystem
validity remain separate work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
