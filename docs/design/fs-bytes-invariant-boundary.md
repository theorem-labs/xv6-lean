# Native byte-view invariant and read crossings

Approved definitions/Spec and proof boundary for the seven new
`FsBytesInvariant{Defs,Spec,PureProofs,RangeProofs,Proofs,RowsProofs,Link}`
modules.
Exact source: `FsBlocks.v:289–331,839–905,933–1158,1618–1705`. The source contracts were reviewed before native proof implementation. The complete fixed
recovery-value function, signed byte/domain geometry and resource carriers
are retained; no BioView abstraction is introduced.

`Capacity` holds the already registered FsBlockGhost three-camera capacity
and the same Disk12 capacity used by the physical disk. Names reuse the
existing six-field `FsBlocks.Names`. The source namespace family is
`logN = nroot .@ "fslogbytes"`, with the byte invariant specifically at
`fsbN = logN .@ "b"`. Public crossings retain the source `↑logN ⊆ E`
premise; later proofs derive the child namespace inclusion, rather than
silently moving the invariant to its parent and obstructing sibling opens.

The actual body existentially binds byte map L, cache map C and exception
set X, in the source order. Its nine conjuncts are:

1. Actual full Disk12 byte-map authority at the logged-view name.
2. One actual cache half for every C entry, using the cache camera.
3. Actual singleton exception authority for X.
4. Exact finite cache domain equals home.
5. Every cache entry has length 1024.
6. Every cache entry outside X has its entire signed map_seqZ byte run in L.
7. L's domain is exactly the union of the signed 1024-byte home intervals.
8. X is a subset of home.
9. At every X block, the entire Xv block's byte run is in L.

Xv is an arbitrary total Int-to-byte-list function fixed outside the body,
as it is in the source invariant. No decoder/well-formedness premise or
fullness of Xv is added. Cache authority is deliberately absent from this
body: source log.lock holds it, while this invariant holds only cache halves.
The exception-set existential remains inside the invariant and can move
only through native resource updates in later recovery rules.

The pure definitions are exact bytes_dom, bytes_tie, bytes_tie_exc and
bytes_exc_val, using the existing signed finite byteRun/map_seqZ operation
and source submap orientation. No flatten-order hypothesis is involved.
Principal contracts include raw byte-range and full-block home membership,
actual invariant-open home membership, sealed full/share read agreement,
and the unsealed full-block recovery crossing with a supplied handle and
explicit exclusion from its exception set. All DFrac variants are retained
for source fractional reads, including discarded and mixed fractions.
Membership is derived from ownership of a nonempty run whose offset is
inside the block and the exact bytes_dom property, never added as a caller
home-coverage premise. Every crossing returns the same byte run and cache
half, and the recovery form also returns the same full exception handle.

The exact region/client rows bind Xv and then home existentially: at, row,
any = row paired with the actual empty seal, and any_at = at paired with
that seal. Their Persistent instances, projections and both full/share
row agreement wrappers are part of this read boundary. The bare row does
not imply a seal or claim recovery complete.

The native proofs will open and close the real nine-leg invariant, using
actual byte authority lookup and half agreement. No opaque invariant
parameter, precomputed cache/byte equality, assumed home membership or pure
snapshot initializer substitutes for a resource. Fresh image-byte allocation,
sub-range log writes, recovery installation, fs_alloc, BioView and whole
region invariant allocation remain subsequent exact source boundaries.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
