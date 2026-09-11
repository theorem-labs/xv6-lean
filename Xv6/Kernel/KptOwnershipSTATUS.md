# Tiered KPT ownership implementation

All eight modules compile. `KptOwnershipProofs.nativeSpec` discharges all
17 approved resource fields; `KptOwnershipGeometry.geometrySpec` discharges
all seven geometry fields. `KptOwnershipLink.registrySpec` instantiates the
existing KptGhost registry, without a new slot or runtime name. Its three
coherence equalities identify the original machine, ghost and view capacities.

`Capacity` contains one actual machine capacity plus mapping/tree/bound
witnesses. Its reducible `.ghost` adapter derives Views from that machine's
existing era. An unmatched view or log capacity cannot be supplied separately.
Both kernel and user slot resources use this same machine/era configuration:

- `Tier.kernel B`: actual eight-byte pinned slot, generated alignment,
  per-byte floors/timestamps, source A/D byte families and original anchors.
- `Tier.user ξ`: existing context-owned physical word at the exact context ID.

`PageValid` requires 4096-byte alignment and the source interval from imported
`Xv6.Generated.KernelMaps.Symbols.end_` (`0x800235c8`) to `0x88000000`.
The lower bound is a reference to the generated symbol, not a copied literal.
`NodeData` independently requires whole-page RAM coverage. `nodeClaim`
contains both pure properties and the identity RW mapping claim at the page
VPN. A mapping ghost claim implies neither geometry property by itself.

Every `pageOwn` contains that persistent node claim and all 512 slot
resources, including unused entries. `indices` represents the source's
ascending integer enumeration after conversion to nine-bit indices; checked
lookup, uniqueness and length are explicit geometry obligations. `treeOwn`
recurses on its natural depth, with `emp` for the child component at zero.
Arbitrary inert children below level zero remain in the description. No
extra distinct-pages hypothesis or well-formed-tree predicate is imposed.

`Spec` records 17 proved fields: component timelessness/persistence, exact slot
forget/alignment/RAM endpoints, the root page-valid projection, and the six
read-only/update page/child/path accessors. Their wands require all extracted
resources back, with the exact requested word/child replacement in update
forms. The path-update result is the real pure `PtTree.setLeaf`; the path
premise retains complete `PtTree.Maps`. No restoration callback or assumed
memory-read result appears. `GeometrySpec` records seven proved pure page and
enumeration laws. The generic `bundle_access` uses the actual native Iris
list-position deletion equivalence and proves every unselected index
unchanged. Page and child accessors instantiate this cut; both path proofs
reassemble the root, middle and leaf pages through their returned wands.
The update accepts any replacement leaf word, exactly as the source spatial
accessor does; validity preservation belongs to the separate pure tree layer.

The recursive `treeOwn` and its `kidsOwn` wrapper are `noncomputable`
IProp definitions. Their ordinary kernel bodies remain transparent and
checked. This suppresses an irrelevant executable recursion companion,
without an unsafe-dependency exclusion or any change to the assertions.

Source map (paper pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`):

- `PageGeom.v:54–69`: page bounds, alignment, validity and base address.
- `PtTree.v:395–416`: page VPN and whole-page RAM property.
- `PtTree.v:911–913,1150–1237`: exact tiers, pinned/context slots and raw-word
  forgetting/RAM facts.
- `PtTree.v:1240–1314`: persistent claims, all-slot pages, depth recursion,
  timelessness and root page-valid projection.
- `PtTree.v:1317–1518`: six spatial accessors with complete reassembly.

Authority-backed concrete-memory extraction, shared invariant opening,
publication, native read/write events and translated execution remain later
layers. This contract does not assert a physical tree from ghost resources
or claim any translated function correctness.

Validation: `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.KptOwnershipLink`
passed all 648 jobs; the path proofs, contract assembly and registry link
compiled in 1.1 s, 863 ms and 910 ms, respectively.
`/tmp/xv6-lean-research/KptOwnershipOwnerAudit.lean` audits every declaration
by its physical origin in all eight modules, with no exclusions, and follows
types, opaque proof bodies and inductive constructors. All 182 physical
declarations passed: only `propext`, `Classical.choice`, and `Quot.sound`,
with no unsafe or partial dependencies. The final result is recorded in `/tmp/xv6-lean-research/kpt-ownership-owner-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
