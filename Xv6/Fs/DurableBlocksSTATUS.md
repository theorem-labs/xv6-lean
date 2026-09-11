# Entry-derived durable allocations

`DurableBlocksDefs` follows FsImg.v3153–3204: preserve the full ordered list of
nonzero slots from every live inode; use the existing exact tail-first failure-aware
`collectNodup` to produce the optional finite extensional block set.

`DurableBlocksProofs` establishes membership, duplicate freedom, per-inode
membership/duplicate freedom, and cross-inode disjointness. Source2763–2839 list
lemmas support the exact ordered equality `inodeEntries = inodeBlocks` under
`SuperblockOK` and original nine-clause `InodeOK`. The global W3 sweep then proves
`entryBlocks = usedBlocks` and `entrySet = usedSet`, without weakening to set
membership. This supplies the missing initial W4 slot-injectivity consequence.
The durable inode coverage reading is also proved.

`DurableBlocksImage` derives the actual initial durable set/bitmap certificate,
all live inode slot injectivity, and cross-inode allocation disjointness from those
general bridges. No literal image recomputation or new host-produced assertion is
needed. Every imported Fs/private/generated-inode theorem cone is audited against
the standard-three foundational axiom allowlist.

Full durable filesystem resource composition and tree vocabulary remain further
porting tasks; these modules do not claim crash consistency or adequacy.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
