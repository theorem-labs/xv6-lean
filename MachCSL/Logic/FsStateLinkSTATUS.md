# Native inode link packing and initial allocation

Frozen source slice for `FsStateInode.v:1323–1467` and
`FsState.v:500–618,688–709,717–817` at xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The six new modules reuse the exact existing `FsState` resource hierarchy,
`LinkFamily` choices and camera elements, and native `FsLink`/`FsTop`
capacities. No camera, node carrier, view name, or Iris world is replaced.
Definitions add only per-entry choice conditions, known-value entry
resources, and the source `fullLinks` collection.

`FsStateLinkChoiceProofs.map_choose` assembles the finite collection's
existential witnesses into one total function. It preserves each original
resource; its fallback applies only outside the map. `FsStateLinkProofs`
uses that law to choose entry types, retaining tokenless entries, the
parent guard, and marker-set conditions. Packing and scattering preserve
the original ghost name. The native `inode_link_packScatter` and
`inode_ghost_iff` theorems identify the complete source node element and
local clause, and `ghost_split` factors the whole ghost column into native
link ownership and the source pure local/geometry facts.

Optional entry ownership is gathered beside an existing accumulator.
An empty map contributes the camera unit algebraically but **does not
create `iOwn` at a chosen name**. The separate scattering direction may
discard that empty contribution. `FsStateLinkGatherProofs` proves this
accumulator discipline for arbitrary finite maps, then obtains the source
whole-family choice and validity from native ownership. `links_valid_tok`
retains the extra ticket inside the validity expression. Present map
entries with empty fragment payloads are never replaced by absent entries.

`FsStateLinkAllocProofs` proves fresh allocation from the exact source
premises: `ElemOK` and native family validity. `boot_alloc_at` accepts
independent link and top maps; the top map carries no added well-formedness
premise. `boot_alloc_root_slack` allocates the combined family and spare
root ticket once, splits their ownership, and returns that ticket beside
the top authority, every top fragment, and all native inode link bundles.
`fullLinks_alloc` and `boot_alloc_full` use the already-proved unconditional
validity of the full supply at home. No duplicate ownership is asserted.
All fields of `LinkResourceSpec` and `LinkBootSpec` have actual proofs.

These are the source's generic fresh-allocation rules within an existing
`GF`. Their intended machine integration is initial epoch-zero setup.
They are not a transport rule, do not consume an old filesystem instance,
and are not wired into reboot or used to replace existing runtime names.
General fixed-name pack/scatter/gather works on already-owned resources.
No new `InvGS` world is allocated. Durable byte ownership, footprint
carving, `fs_snap`, and `P_dur` allocation remain separate dependencies.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsStateLinkAllocProofs`
passes **266 jobs**. The proof modules elaborate in about 0.8–0.9 seconds.
There are **29 named theorems**. A fresh physical-origin audit checks all
**52 declarations** across the six modules, their transitive types,
bodies, and referenced constructor fields. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; no unsafe/partial semantic
dependency and zero exclusions. The audit source is retained at
`/tmp/xv6-lean-research/FsStateLinkOwnerAudit.lean` in the working environment.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used. Root
source review of the definitions/interfaces and full proof checkpoint passed; see
`docs/reviews/fs-state-link-review.md`. Existing frozen files and umbrellas were not
changed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
