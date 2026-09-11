# Exact filesystem footprint and native ledger carve

Frozen source slice: `FsDurAlloc.v:80–800` at xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, with the exact inhabitant from
`FsNode.v:36–37` and `DinodeEnc.v:64–65`.

The seven modules preserve all six slot constructors: superblock,
bitmap, inode record, data slot, indirect block, and free-pool block.
The source default node has empty record-address and entry lists; it is
kept separately from a well-shaped bare inode. Data slots read a missing
owned block as the empty list, rather than the file reader's zero block.
The footprint includes every stored inode and every owned data slot,
independent of EOF, together with all indirect roles and every signed
pool index in `[0, size)`. A used pool slot or absent indirect block has
an empty footprint. Block zero is included in the pool when size is
positive. Source fields and arbitrary malformed carriers remain total.

`FootprintProofs` proves that every valid slot is a slice of the flattened
block map, with its exact nonnegative offset and at-most-1024 endpoint.
It derives full block sizes directly from `Snapshot.Bytes.blockSize`.
`SeparationProofs` spends the existing snapshot metadata, ownership,
representation, cross-node disjointness, and slot-injectivity clauses.
It accounts for two records sharing an inode block by distinct offsets.
No independent disjointness, validity, or reachability premise replaces
these source obligations.

`FamilyProofs` proves both directions of membership versus source slot
validity and proves the complete family duplicate-free. Lean finite-map
key enumeration may differ in order from Rocq's `elements (dom ...)`;
only membership, uniqueness, and separation govern the resource bridge.
No raw cross-language equality of those ordered lists is claimed.
`LedgerProofs` proves native ownership of the selected left-union is
exactly the separating conjunction of the disjoint family. It then
carves a provided ledger once, returning the exact difference between
the whole map and that selected union, plus an arbitrary frame. This
retains the remainder that the source affine entailment may discard.

`provided_image_carve` specializes the result to the actual Disk camera
at slot 12 in the current registry. The supplied whole image may strictly
contain the flattened block map; its coverage premise has the correct
submap direction. The result retains the exact original map authority,
all unselected bytes, and the caller's frame. No byte authority or ghost
name is allocated or replaced. All fields of `FootprintSpec` and
`CarveSpec` have actual proofs.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsDurAllocLink`
passes **438 jobs**. There are **33 public named theorems**, plus one
private injective-map helper. Kernel regressions check the source default
record's 12-byte encoding, empty missing data, pool block zero, and empty
used-pool footprints. A fresh physical-origin audit checks all **246 declarations** in the seven
modules and their transitive declaration types, bodies, and referenced
constructor fields; only `propext`, `Classical.choice`, and `Quot.sound`
are permitted, with no unsafe or partial semantic dependency and zero
exclusions. The audit source is retained at
`/tmp/xv6-lean-research/FsDurAllocOwnerAudit.lean` in the working environment.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

The next source dependencies are regrouping the slots into the exact
nested `FsState.state`, then the native `fs_snap` and `P_dur` definitions
and their epoch-zero allocation rules. This checkpoint does not claim
those allocation results, use pure `Snapshot.OK` as a native resource,
or allocate another Iris world. Existing frozen files and umbrellas were
not changed.

Coordinator full-file/source review and a fresh independent full-cone audit passed;
see `docs/reviews/fs-dur-alloc-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
