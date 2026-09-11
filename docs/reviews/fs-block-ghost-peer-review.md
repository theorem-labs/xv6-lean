# Independent filesystem block-camera review

Read all five modules and the complete source contracts in
FsBlocks.v:96–175,776–832. The three native cameras retain signed block
keys, arbitrary byte-list cache values, Boolean dirty values and exact
Unit-to-finite-set exception entries. The Unit ordering is scoped, with
checked laws and no numeric key substitute.

Client and machinery cache resources use exact half fractions; machinery
retains the matching dirty half at false/true. Native two-half updates
first prove old agreement and authoritative lookup, then update and
return both new halves with the full authority. The exception operations
use actual singleton authority, full handle and discarded empty seal.
Arbitrary same-name updates require both full resources, while sealing
consumes only the empty handle. These match the source statements.

Slots 39–41 preserve all previous slots and 42 upward. The signed byte
capacity is explicitly the existing machine Disk12 capacity. No byte
invariant, BioView, recovery-completion oracle or fresh replacement world
is hidden in these contracts. The exact six source names are reused.

Independent fresh physical-origin audit passed all 225 logical declarations
and their full opaque-value/type/constructor dependencies. Standard three
axioms only, no runtime exclusions, unsafe/partial logical dependencies
or initial snapshot allocation calls. Command:
`PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py env lean
/tmp/xv6-lean-research/FsBlockGhostOwnerAudit.lean`.
Evidence: `/tmp/xv6-lean-research/fs-block-ghost-peer-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
