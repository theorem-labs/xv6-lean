# Independent native byte-window review

Codex coordinator read all eight TsoContextBytes and TsoContextBytesReadWP
modules and checked their use of the existing context and actual read-event rules.
PASS. Every byte is read at the same arbitrary permitted view, with the full
live era restored. Generic widths include zero and impose no alignment.
Agreement follows actual byte-camera agreement. Splitting uses equal fractions
for bytes and timestamps; persistence updates both, and pristine discarded
resources stay discarded. Subwindow extraction returns a linear restoration
wand; modular address reindexing and byte equality are proved explicitly.
The native read internally derives the all-successor premise and preserves the
running context, exact window and optional reservation through the real guarded
continuation. It does not assume a read-value oracle.

Fresh independent `tools/lake.py env lean /tmp/xv6-lean-research/TsoContextBytesAudit.lean`
passed all 53 declarations across all eight origins, including types, opaque
bodies and constructors, with the standard three axioms, zero exclusions and no
unsafe/partial logical dependencies. Actual kernel text extraction and virtual
fetch composition are subsequent work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
