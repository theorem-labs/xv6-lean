# Independent top-map retag review

Read both modules against `InodeRegion.v:3294–3340`. Ordinary retag
updates native top authority and full fragment only with exact Local
validity. Armed retag first derives actual registry lookup from the
held full receipt, uses its inode membership to justify suspension of
the clean row, and returns that identical receipt. Both rules preserve
parked shares, the other authority, and the native invariant masks.
The updated map uses the actual full top-map camera; no new camera,
allocation, abstract validity oracle or filesystem completion claim occurs.

Fresh independent full audit passed all 14 declarations, private helpers,
opaque bodies, declared types and constructor dependencies. Standard three
axioms only; no runtime exclusions or unsafe/partial logical dependencies.
Command: `PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py env lean
/tmp/xv6-lean-research/IcacheTopRetagOwnerAudit.lean`.
Evidence: `/tmp/xv6-lean-research/icache-top-retag-peer-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
