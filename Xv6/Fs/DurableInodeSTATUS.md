# Durable inode predicate

`DurableInodeDefs` ports FsImg.v2466–2740: the five Boolean groups and eight
`fs_inode_dok` fields, plus the same live-inode sweep over the advertised range.
Unlike initial W3, there is no positive nlink floor, and every nonzero direct,
indirect-root or indirect-data entry may remain allocated beyond file size.
Each such allocation must still name a data block. Below-size coverage remains
mandatory; total list lookups and arbitrary signed superblock fields are retained.

`DurableInodeProofs` proves Boolean/record equivalence, the source size-change rule
with explicit new-size coverage, W3 implication for a record and the whole sweep,
and the bounded sweep projection. Kernel regressions distinguish zero-link orphans
and beyond-size allocation from W3, and reject beyond-size metadata references.
`DurableInodeImage` derives the actual200-inode durable sweep from the existing
full W3 certificate. All theorem cones use only standard foundational axioms.

The durable entry-derived used-block set and its W3 correspondence are the next
source layer. This file does not claim durable whole-filesystem validity.

Authorship note: researched and written by OpenAI Codex on Jason Gross's behalf.
