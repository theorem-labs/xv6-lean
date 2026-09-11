# Native durable byte readback review

The coordinator read all five Lean modules and all 385 lines of the pinned
`FsDurRead.v`. The native readers match the source's arbitrary fractional
ownership and existential snapshot authority contained in flattened bytes.
Nonempty runs retain nonnegative offset and within-block bounds; every block
reader retains the explicit full-block premise. The signed block identity and
prefix/suffix reconstruction are derived from actual map/list lookup.

The overlap rules extract two separately owned occurrences at the shared
byte; the invalid joined fraction refutes overlap. The finite free-pool rule
then derives membership in the used set from an actual nonempty owned run.
No reader allocates a ghost name, invokes an initial constructor, assumes slot
injectivity, or infers full block lengths from the snapshot's Shape clause.

Validation: the 407-job combined build passed. The coordinator reran the
physical-origin audit for all 56 declarations and complete transitive bodies
with `allowOpaque := true`, including referenced constructors: only the three
standard axioms, no unsafe/partial dependency, zero exclusions.

Review: approved as the complete bounded FsDurRead source slice. Inode,
within/across-inode disjointness and used-set readback remain separate work;
full snapshot readback and runtime transport are not claimed here.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
