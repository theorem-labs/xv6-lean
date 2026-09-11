# Native cache, dirty flags and recovery exceptions

Approved initial boundary: `FsBlocks.v:96–175,776–832` and the exact
`fsLogG` declaration in `Xv6Cameras.v:361–385`. Definitions and the public
Spec are the review checkpoint before proof implementation. Owned future
modules are `FsBlockGhost{Defs,Spec,Proofs,Link}` and STATUS. A tiny
`FsBlockGhostKey` infrastructure module gives Unit its scoped constant-equal
order and checked transitivity/equality laws for the native extensional map.
No global Unit ordering instance is introduced.

The three distinct native GhostMap capacities are:

| Reserved slot | Key | Complete value |
| --- | --- | --- |
| 39 | Int block number | List (BitVec 8) cache bytes |
| 40 | Int block number | Bool dirty flag |
| 41 | Unit | finite extensional set of Int exception blocks |

The registry will extend the frozen top registry at precisely those slots,
preserve 0–38 and 42 upward, and export existing capacities including the
unique signed Disk12 byte camera. There is no second logged-byte camera.
The existing `FsBlocks.Names` six-field record is reused verbatim: cache,
dirty, bytes, link, top and exceptions. No shortened or alternate naming
record, global name equality assumption or freshly allocated world appears.

`chalf` is an actual cache element at `DFrac.own (1:Qp).half`. `mclean`
is that cache half paired with a dirty half at false; `mdirty` pairs it
with a dirty half at true. Lists are arbitrary at this resource boundary,
with no added 1024-byte validity premise. Source block fullness belongs to
later byte-invariant and buffer predicates. The source agreement contracts
return machinery bytes equal to client bytes, in that order. The cache
update and dirty flip require actual full authority plus both held halves,
return their prior agreement and authoritative lookup, and return the
updated authority and both updated halves. Updating with only authority
or only one half is not exposed as this source operation.

`exc_auth` owns the exact singleton Unit map to X, `exc_own` its full native
element, and `exc_sealed` its discarded element at the empty set. Allocation
produces actual singleton authority and its full fragment in the same world.
Agreement and sealed-empty are native authoritative lookup consequences.
Update requires the authority and full handle, retaining the same name;
its source contract allows arbitrary X→X′, not only a shrinking operation.
Sealing consumes the empty handle and persists that element. There is no
pure flag substituted for the discarded fragment, no requirement to hold
authority when sealing, and no assumed recovery-completion fact.

The public Spec contains both clean/dirty agreement laws, both two-half
updates and all five exception allocation/agreement/sealed-empty/update/seal
laws. Timeless resource instances and Persistent seal are native consequences
to be proved after this contract review. Allocation carries an arbitrary
caller frame; no rule replaces an existing authority with a fresh one.

Explicitly deferred: the source `BioView` structure and its dependencies,
full `fs_alloc`, byte-range operations not already supplied by the frozen
Disk12 bridge, and the complete nine-leg byte invariant, its recovery
operations, row/seal packaging and region invariant. Those need their own
exact source contracts; neither an opaque BioView nor an assumed byte
invariant will be introduced here to stand in for them.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
