# Finite native inode-region body and actual image specialization

The five `IcacheRegionBoot{Defs,Spec,DistributionProofs,Proofs,Link}` modules
and separate two-module `Xv6/Fs/IcacheRegionImage{Defs,Proofs}` leaf are frozen
after owner validation. The approved design is
`docs/design/icache-region-boot-boundary.md`.

| Exact pinned source | Lean mapping |
| --- | --- |
| `InodeRegion.v:2860–2912` | `block`, `coveredRegistry`, `body`: actual sixteen-slot block, full covered registry and arbitrary record-map authority |
| `IcacheBoot.v:420–487` | `flat_sixteen`, `set_flat`, `slots_rows`: checked finite-set to flat-list to sixteen-row distribution with total decoder defaults |
| `IcacheBoot.v:591–605` | `dummyRegistry`, lookup/coverage/key laws: exact region-to-(1,1) map |
| `IcacheBoot.v:708–724` | `registry_insert`: actual native bulk insertion into the supplied empty authority, same name, returning every full row |
| `IcacheBoot.v:724–851` | `slots_from_clients`, `body_from_rows`, `bootstrap_body`: record-only allocation, native component routing and complete finite body assembly |
| `FsCfgSnap.snap_ireg_premises` | Literal `decoded_premises`: all six universal image decoding conditions from the checked full snapshot theorem |

The body owns a full arbitrary record map, a block resource for each of the
nib blocks, and a full registry map with the exact signed-region coverage
condition. The record map keeps negative marker keys and all other entries;
it is not restricted to the nonnegative region. Every block retains its
existential well-formed sixteen-record list, record-map coupling, source
byte runs and sixteen complete actual native slots. No slot is replaced
by a supplied opaque invariant or a pure predicate.

The exact dummy registry has (1,1) values for all and only the finite region
keys. These values are names stored as data; they do not allocate tickets
or committed escrow resources. Native insertion consumes the caller's
existing empty full authority and preserves its ghost name. The finite-set,
flat-list and nested-row bridges preserve every inode once, including empty
regions and the padded tail, using proved membership and no-duplicate laws.

Generic bootstrap takes full 1024-byte blocks, the source 32-bit bound and
six universal decoded-region premises. Its native inputs are existing byte
runs, six client columns for every region inode, a same-name empty registry,
and an arbitrary frame. The columns are zero unclaimed/unfrozen reference
authority, zero observation authority, count/mirror halves, count/type-indexed
filesystem link custody and conditional free-node top ownership. Only the
source record/marker camera is freshly allocated, via the existing checked
record/byte prelude. Every other supplied resource is distributed without
replacement. The result returns the full body, all source outside
record/marker fragments and the exact caller frame under one basic update.

The literal leaf selects all thirteen actual inode blocks from the checked
artifact. Their lengths and indexing are proved against `Image.blockView`;
the six premises follow from `Image.snapshot_ok` and the existing generic
snapshot-to-region theorem for all 208 padded inodes. No new bytes, generator,
native computation certificate or input assumption replaces these checks.
The leaf still requires the native byte/client/registry resources explicitly.
Pure snapshot validity does not allocate those resources.

The source generic `ireg_alloc` does not equate its byte start with
`icfg_ist`. The generic body deliberately preserves that freedom. The
literal leaf uses `imageNames`, updating only `epoch.inodeStart` to the
actual 33 and retaining every ghost name and the observation-name function.
Checked geometry laws include the exact `iblkOf = inodeBlock` relation.
Thus the literal receipt and byte locations agree explicitly; this is not
an unmentioned premise or a strengthening of the generic source theorem.

Validation: `python3 tools/lake.py build Xv6.Fs.IcacheRegionImageProofs`
passes all 636 jobs. There are 14 named generic theorems and ten literal
leaf theorems. Fresh physical-origin owner audits
`/tmp/xv6-lean-research/IcacheRegionBootOwnerAudit.lean` and
`/tmp/xv6-lean-research/IcacheRegionImageOwnerAudit.lean` cover all 37 generic
and 18 literal declarations, including private/generated helpers, opaque
bodies, types and datatype constructors. Only `propext`, `Classical.choice`,
and `Quot.sound` occur; zero roots are excluded and no unsafe/partial or
`FsDurSnapshot.Initial` dependency occurs. The generic files import no
literal image leaf. Existing capacities through slot 37 are reused; no
registry extension or new camera is introduced.

This closes finite native body assembly and its actual-image specialization
from supplied clients. Region invariant allocation (`ireg_reg`/`ireg_inv`),
free-pool/escrow invariant payloads, allocation of the whole native client
state and complete filesystem initialization remain separate obligations.
The source `fs_bytes_row` and `ftop_inv` can travel unchanged in the frame;
neither is silently assumed or substituted for a missing body here.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
