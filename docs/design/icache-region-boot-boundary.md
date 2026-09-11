# Finite native inode-region body bootstrap

Approved files: `IcacheRegionBoot{Defs,Spec,DistributionProofs,Proofs,Link}`,
STATUS, and separate literal leaf `Xv6/Fs/IcacheRegionImage{Defs,Proofs}`.
Source boundaries are `InodeRegion.v:2860–2912` and
`IcacheBoot.v:420–487,591–605,643–851`. Existing native slot, record and byte
preludes remain unchanged.

The exact block owns an existential list of sixteen well-formed Dinodes,
its coupling to the supplied authoritative record map, the existing sixteen
record byte runs and sixteen complete actual slots. The covered registry
owns an existential finite Int-to-escrow-name-pair map with the source
0≤z<16*nib coverage predicate and actual full map authority. The body owns
an arbitrary record map's full authority, nib blocks and the covered registry.
It retains all record-map entries, including the negative marker shadows;
no carrier restriction to positive keys is introduced.

The registry boot operation inserts the exact finite region map to pair
(1,1) into the supplied empty authority at its existing name. It uses the
native bulk insertion rule and returns every full fragment. The dummy names
are data only: no escrow ticket or committed fragment is minted for them.
Checked set/flat-list/sixteen-row reindexing distributes every region element
once, including the padded inode tail. All source integer bounds and total
decoder defaults are preserved.

Generic bootstrap inputs are existing region bytes, six per-inode client
columns (unclaimed/unfrozen zero reference authority, zero observation
authority, count/mirror halves, count/type-indexed filesystem link custody
and conditional free-node top ownership), the same-name empty registry
authority, and an arbitrary frame. It retains the exact full-block and
32-bit region bound and the existing universal six-decoding-premise contract.
Only the source record/marker camera is freshly allocated, through the
already checked record-and-byte bootstrap prelude. The proof populates the
provided registry, applies pointwise slot boot at every region inode,
assembles the full body and returns every outside record/marker plus frame.
There is no new camera, client-resource allocator, invariant assumption or
replacement registry authority.

The literal leaf selects the actual thirteen `Image.blockView` inode blocks.
Its six decoding premises follow from the existing full actual snapshot
validity theorem and `SnapshotConfig.snap_ireg_premises`, with unchanged
bytes and readers. No new byte generator, host-side assertion or narrowed
checker substitutes for that proof. Native client resources remain inputs;
the leaf does not pretend that pure snapshot validity allocated them.

The generic body retains the source freedom between its byte-region `start`
and `names.epoch.inodeStart`: `IcacheBoot.ireg_alloc` has no equality premise
between `inodestart` and `icfg_ist`. The literal leaf explicitly uses
`imageNames`, which updates only `epoch.inodeStart` to the actual 33. All
reference, coupling, boot, transaction, registry and epoch ghost names and
the observation-name function are retained. Its checked `imageNames_iblk`
law ties the receipt block calculation to the actual filesystem
`inodeBlock`; no final configuration tie is silently assumed.

This stage stops before region invariant allocation. `fs_bytes_row` and
`ftop_inv` may be retained in the caller frame but are not assumed by the
body. Constructing the exact `ireg_reg`/`ireg_inv`, free-pool payload and
whole native filesystem boot remains subsequent work. Generic files import
no actual-image leaf. Definitions and statements precede proofs, and the
final physical-origin audit includes all opaque bodies, types and datatype
constructors with the standard three axioms only.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
