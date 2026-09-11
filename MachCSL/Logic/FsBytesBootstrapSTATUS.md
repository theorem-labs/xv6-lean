# Complete native block and logged-byte bootstrap

Frozen seven modules: FsBytesBootstrap Defs/Spec/PureProofs/GrowProofs/
MintProofs/Proofs/Link. The full three native contracts are proved, including
all source output columns. Source mapping is pinned FsBlocks1424–1504
(byte_map_grow), 1514–1565 (fs_bytes_alloc), 1709–1730 (polymorphic filter
split/domain), and 1738–1800 (fs_alloc).

The same-name growth rule proves fresh byte-domain disjointness from the
source full-block and block-set premises, then uses native bulk insertion.
It extends the supplied byte authority and returns every new full byte run
plus the unchanged arbitrary frame. The existing guarded flatten theorem
justifies the bulk implementation independently of finite-map enumeration;
no equality for overlapping oversized blocks is assumed. Signed negative
blocks and empty sets/maps are included by the general proofs.

The byte mint consumes the supplied cache-half ledger and allocates fresh
logged-byte and exception names in the existing world. It builds the actual
nine-leg invariant at fsbN with the committed value function fixed outside
the invariant body. Raw cache values are retained; equality with committed
bytes is needed only outside the arbitrary exception set. The full
exception handle and all full committed byte runs return to the caller.

The complete fs_alloc allocates cache and clean-dirty authorities and
splits every element through native fractional laws. Its output preserves
both supplied link/top names, both authorities, the actual byte invariant,
the full exception handle, machinery plus the SECOND dirty half over every
covered block, exclusive committed byte runs on home, and parked raw cache
halves outside home. No client column is dropped. Exact complementary
filter and domain laws are also exported for arbitrary payload types,
matching the source helpers beyond their concrete byte-list use.

The Link reuses slots 12/39/40/41 in the existing registry, with checked
identity to the actual machine disk camera and an explicit existing InvGS
link. Names for cache/dirty/logged bytes/exceptions are fresh native ghost
names; link/top names are supplied. Temporary unused byte/exception name
fields in the construction are replaced before producing the final record;
no resource is allocated at those temporary fields.

This is the source's fresh logged-view mint. It does not invoke an Initial
durable allocator, allocate a new Iris world, update physical disk bytes or
infer physical content from framing. Existing physical authority and other
resources can be framed unchanged. Full FsBoot/FsCrash caller composition
must establish the raw/committed disk relationship and supply later native
client distribution. Recovery sealing/installation, log/Bio/config
invariants and complete filesystem initialization remain subsequent work.
The contracts contain no once-only linear authorization claim.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsBytesBootstrapLink`
passed 509 jobs; final new proof modules each compiled in about one second,
without new warnings. There are 34 public named theorems plus one private
fractional splitting helper. The owner audit checked all 74 logical
physical-origin declarations in all seven modules, including private and
generated roots and every transitive opaque body, type and constructor.
Only propext/Classical.choice/Quot.sound occur, with zero excluded roots,
no unsafe/partial logical dependency and no Initial allocation dependency.

Direct callers in these seven modules, checked from elaborated types and
opaque bodies: byte_map_grow is used by fs_bytes_alloc and actual;
fs_bytes_alloc is used by fs_alloc and actual; fs_alloc is used by actual.
The actual/nativeSpec chain packages the checked contracts. There is no
literal image or runtime caller in this frozen boundary yet. Evidence:
`/tmp/xv6-lean-research/FsBytesBootstrapOwnerAudit.lean`,
`fs-bytes-bootstrap-build.log` and `fs-bytes-bootstrap-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
