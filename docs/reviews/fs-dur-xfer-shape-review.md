# Durable footprint run correspondence review

The coordinator read all five modules and compared them with FsDurXfer.v
sections 3a–d, lines 584–976. The record run uses the exact wrapped 32-bit
inode index. Data runs retain all stored block-map entries and the conditional
indirect run. The source NodeLens predicate requires stored data lengths and
the nonzero indirect block's encoded length; no record-validity or geometric
condition has been added.

Free-pool extraction names the bytes already owned by the source in an
existential finite map. Its domain is exactly the listed unused blocks and
its entries are full blocks. The reverse direction uses source list uniqueness
and that domain condition. Signed negative sizes retain the empty source
range. The whole filesystem footprint converts in both directions through
the exact Shape predicate. Arbitrary uniform DFrac versions follow through
the constant-share view, without disjointness or Snapshot.OK assumptions.

The independent coordinator audit checked all 81 physical declarations,
full opaque bodies and constructor dependencies. It passed with only the
three standard Lean axioms, zero exclusions and no initial-allocation
dependency. The linked build passed 423 jobs. This prerequisite is approved;
same-name installation and source-instance transport remain separate layers.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
