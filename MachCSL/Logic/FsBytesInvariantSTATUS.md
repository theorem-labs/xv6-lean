# Native byte invariant and principal read crossings

The seven `FsBytesInvariant{Defs,Spec,PureProofs,RangeProofs,Proofs,RowsProofs,Link}`
modules are frozen after owner validation. The approved contract is recorded
in `docs/design/fs-bytes-invariant-boundary.md`.

| Exact pinned source | Lean mapping |
| --- | --- |
| `FsBlocks.v:289–331` | Exact `logN`, child `fsbN`, checked child/parent mask inclusion |
| `839–905` | All four pure byte-tie/domain predicates, complete nine-conjunct body and actual native invariant |
| `569–684` (needed source prerequisites) | Native `range_map`, `range_lookup`; exact same-start, equal-length byte-run agreement |
| `933–989,1070–1120` | All-DFrac nonempty range/full block home derivation and actual invariant-open membership |
| `994–1064,1123–1158` | Sealed full/share agreement and unsealed full-block exception-handle agreement |
| `1618–1705` | Exact existential home/value rows, actual seal pairing, projections and full/share read wrappers |

The body existentially binds the logged byte map, cache map and exception
set in the source order. It retains actual full Disk12 authority, each
cache entry's half, singleton exception authority, exact cache-domain/home
equality, full 1024-byte cache lengths, tie outside exceptions, exact logged
byte domain, exception inclusion in home and logged-value inclusion on the
exception set. The recovery-value function stays fixed outside the body.
The cache's full authority is absent, as in the source: this invariant owns
halves while the log lock separately owns that authority. Arbitrary signed
keys, byte lists and fixed value functions remain the source carriers.

The namespace is exactly `nroot .@ "fslogbytes" .@ "b"`; public crossings
retain the parent `logN` mask condition. The native proofs open that child,
not the parent, preserving the future sibling superblock park's independent
mask. The actual InvGS and existing cameras are used; there is no opaque
invariant assumption or alternate resource implementation.

The byte-range map bridge converts the actual owned list of native elements
into the existing finite signed map_seqZ ledger. Native authoritative lookup
then proves its submap relation. The first byte of a nonempty run, with its
offset inside the block, lies in the exact logged domain and identifies the
unique home block by signed integer interval arithmetic. Full block
membership follows from its stored length 1024. No caller home-membership
premise, upper bound on the entire sub-range or unsigned-address coercion
is added. The statements preserve arbitrary DFrac, including discard and
mixed fractions.

Native cache-half agreement identifies the machinery bytes with the cache
entry at the derived home block. Both the owned byte run and that entry's
byte run are submaps of the same actual logged authority. Their equal
lengths imply list equality, proved for arbitrary signed starts and lists.
All reasoning is kernel checked and independent of concrete image bytes.
The cache lookup can be borrowed for this pure equality; the entire cache
half map remains available to close the invariant unchanged.

The sealed crossing reads the actual discarded-empty exception fragment
against its authority. The recovery crossing instead reads the actual full
handle and requires the source explicit block exclusion. It returns that
same full handle, without sealing or updating it. Both return the original
byte run and cache half and close with the original L/C/X and fixed Xv.
The block and fractional forms share a checked generic read theorem.

`atHome` binds Xv; `row` then binds home. `any` is exactly row plus the native
empty seal, and `anyAt` is its named-home form. The bare row does not imply
recovery completion. All Persistent projections/composition and full/share
row crossings are checked. The Link adds no slot: it reuses the block
cameras through 41 and the signed byte camera at 12, with a checked equality
to the actual machine-era disk capacity. Existing names remain explicit.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsBytesInvariantLink`
passes all 502 jobs. There are 30 named theorems, two Timeless instances and
five Persistent instances. Fresh
`/tmp/xv6-lean-research/FsBytesInvariantOwnerAudit.lean` covers all 93 logical
declarations from all seven physical origins, private/generated helpers,
opaque bodies, types and datatype constructors. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; zero roots are excluded and no
unsafe/partial or `FsDurSnapshot.Initial` dependency occurs.

This closes the exact invariant definition and read/row interface. Fresh
byte-map construction and invariant allocation from the source cache,
sub-range log writes, recovery installation, complete fs_alloc, BioView,
region invariant assembly and full filesystem boot remain subsequent
source obligations. No initial allocator or pure snapshot constructor is
used to supply the resource inputs of these runtime read laws.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
