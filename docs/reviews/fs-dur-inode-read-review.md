# Native durable inode readback review

The coordinator read all four modules and the corresponding FsDurSnap §7b
source. The block, indirect and pool readers preserve explicit full-block
premises and use the existing snapshot authority. The inode reader uses the
unsigned-range record-address bridge, the exact 64-byte record encoding
under Local, and the original Snapshot.InodeRead conclusion.

Slot injectivity is derived from native separation. Distinct data entries
are extracted with delete followed by lookup; data and indirect entries are
different conjuncts. The proof covers all 269 slots and uses Local only to
recover stored data for nonzero address slots. It does not assume the
injectivity it proves, or restrict ownership to the file's visible length.

Validation: 416-job build; independent coordinator audit of all 40 physical
declarations, including full opaque proof bodies and constructor dependencies,
passes with only standard three axioms, zero exclusions and no unsafe/partial
dependency. Approved as bounded inode readback. Across-inode/metadata
coupling, full snapshot readback and source-instance transport remain open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
