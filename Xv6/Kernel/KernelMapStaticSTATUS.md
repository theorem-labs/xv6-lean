# Static kernel map: implemented and independently reviewed

All seven pure and five native resource contracts are implemented. The
full build passed 655 jobs; coordinator and independent peer audits each
checked all 79 physical declarations, full opaque bodies, types and constructor
dependencies. Only the standard three axioms occur; no unsafe/partial
dependency and no exclusions. The exact
source classifier covers seven RX text pages, 32,761 RW data pages and
16,386 RW device pages. No source-range narrowing or new camera is introduced.

This is the source static ghost map and its persistent claim bundle. Physical
page tables, dynamic trampoline/stack mappings, concrete era installation,
hardware configuration construction and boot reachability remain separate.
See docs/design/kernel-map-static-boundary.md and
docs/reviews/kernel-map-static-peer-review.md.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
