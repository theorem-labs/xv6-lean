# Logged filesystem byte-view bridge

This ports the complete 127-line FsBytesGamma.v bridge at the paper's
arxiv-v1 pin, plus the six-field FsBlocks.fs_names record and the concrete
byte/block predicate definitions at FsBlocks.v lines 341–396. The logged
view retains its own bytes, link and top names. Cache, dirty and exception
names remain data fields for the later block/log layers.

Both logged and durable views use the existing signed disk-byte camera,
at slot 12 in the concrete registry, with separate runtime names. Byte
offsets remain signed and block predicates retain the exact 1024-byte
length condition. Full and fractional byte-range/block conversions hold
by kernel conversion. Native exclusivity, fraction splitting and timelessness
come from that same camera. The additional source-agreement law connects
the logged view to its own authoritative map for later transfer.

No resource or fresh name is allocated. No equality between this map and
RAM, cache contents or physical durable media is asserted. Those ties require
the actual block/log invariant and its operational preservation.

Validation: 405-job linked build; all 40 physical-origin declarations and
their full opaque bodies and constructor dependency cones pass the standard
three-axiom audit, with zero exclusions and no initial-allocation dependency.
Independent peer review passed; see
[the report](../../docs/reviews/fs-bytes-gamma-review.md).

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
