# Native filesystem footprint and run shape

Frozen bounded port of `iris/FsDurXfer.v` §§3a–d, lines 584–976, at
`arxiv-v1` (`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). Five modules
provide the source's structural run lists and both directions of their
native resource correspondence. There are 27 named public laws and two
private finite-map lookup helpers.

The run definitions retain every source detail: record addresses use the
wrapped unsigned-32-bit inode index; stored data maps include allocations
beyond file size; an indirect run occurs exactly when its address is
nonzero; inode maps and free-pool maps are enumerated through the lawful
finite-map interface. The whole list orders the superblock and bitmap
before inode runs and pool runs. Byte lists and signed addresses are not
normalized or decoded.

The three shape predicates retain exactly the source's conditions:

- `NodeLens` asserts full lengths for stored data blocks and, conditionally
  on a nonzero indirect address, the indirect encoding. It contains no
  record well-formedness or 64-byte record-length condition.
- `PoolPM` states that the map domain is exactly the listed unused blocks,
  and that every stored block is full length. The map's byte values are
  obtained existentially from the source resources.
- `Shape` contains only the superblock byte length, pointwise `NodeLens`,
  and `PoolPM` for the exact signed pool sequence. Bitmap length is a
  theorem of its encoding, not an additional caller premise.

The inode proofs correspond to lines643–770. Their forward directions
extract the source's length facts and return its run resources. Reverse
directions require only those length facts. The free-pool proofs follow
lines786–905: induction over a duplicate-free index list collects unused
entries into a finite map, while the reverse proof deletes each selected
map entry before continuing. Both directions preserve present bytes and
exact absent-key behavior. Negative signed pool sizes produce an empty
sequence; `negative_pool_domain` proves the corresponding map is empty.

The whole-footprint laws at lines919–976 return an existential pool map,
the exact Shape, and run ownership. Their reverse consumes run ownership
under Shape and reconstructs the original byte footprint. Fractional
wrappers use the existing constant-share view and uniform run tagging;
they accept every `DFrac`, with no fraction-validity premise at this
structural stage. No disjointness, `Local`, `Snapshot.OK`, geometric
bound, or allocation is needed or silently added.

Finite-map enumeration order is the Lean container's lawful order. These
proofs relate the actual enumeration to the actual native map big-op;
they do not assert equality of raw lists with Rocq's internal map order.
The run/disjoint-union laws support the later ownership-derived transport
without introducing an order assumption on map carriers.

Validation: `python3 tools/lake.py build
MachCSL.Logic.FsDurXferShapeProofs` passes 423 jobs. A fresh physical-origin
audit checks all 81 declarations and all transitive types,
theorem/opaque bodies (`allowOpaque := true`), and referenced constructor
fields. Only `propext`, `Classical.choice`, and `Quot.sound` occur;
no unsafe or partial semantic dependency, zero exclusions. Explicit
rejection of `FsDurSnapshot.Initial` dependencies passes. Working audit:
`/tmp/xv6-lean-research/FsDurXferShapeOwnerAudit.lean`.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

The next separate obligations are resource installation with the exact
unclaimed-byte remainder, source-instance transport, and epoch cloning.
No runtime mint or complete crash refinement is claimed by this slice.

Coordinator source comparison and independent audit also passed;
see [the review](../../docs/reviews/fs-dur-xfer-shape-review.md).

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
