# Complete native snapshot readback

Frozen bounded port of the four readback laws in `iris/FsDurSnap.v`
§§7b–8, lines 1269–1403, at `arxiv-v1`
(`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). Three modules derive the
existing `Snapshot.OK` predicate from the existing native six-leg
`fsSnap`, with the source's explicit `BlocksFull` premise.

The four laws are `fs_snap_read_ok`, its resource-preserving keep form,
`P_dur_tie`, and its keep form. The latter two existentially hide the
already owned names and state. Keep forms return the exact same native
snapshot or `Pdur`; they do not allocate a replacement. There is no
`Snapshot.OK` premise, pure-input mint, fresh name, or extra oracle.

All 21 existing snapshot byte fields are assembled:

- Full block lengths come from the explicit committed-view premise.
- Superblock and bitmap bytes come from native authority/fragment reads;
  parsing comes from the native state's pure column.
- Free-pool coverage comes from owned full blocks and byte agreement.
- Inode range is derived from Geometry's rounded region and ushort bound.
- Representation and local validity come from the inode ghost column.
- Record slices, stored data bytes, nonzero indirect blocks, and all-slot
  injectivity come from the reviewed per-inode reader.
- Advertised and padded inode domains, superblock validity, region bounds,
  and directory-local conditions come from the exact Geometry fields.
- Link-family choice and validity include the separately owned extra root
  token, through native `links_valid_tok`; root slack is not assumed.
- Metadata membership in the used set, owned-block membership and metadata
  exclusion, and cross-inode disjointness come from native coupling.
  Their bounds follow from Shape only after committed-map presence has
  been reconstructed by the relevant byte reader.
- The final committed-map domain bound is exactly the existing Shape leg.

`Snapshot.OK` remains the existing conjunction of these 21 byte fields
and all per-inode local clauses. No source definitions or carriers changed.
The two derived Geometry helpers correspond to `FsState.v` lines129–154;
`pureState_local` and `footprint_one` expose existing resource definitions.
`ReadbackSpec` packages the four proved laws, and the registry link supplies
the actual Disk slot12, FsLink slot23, and FsTop slot25 capacities. Both top
legs remain part of the unchanged input snapshot, even though the source
readback does not need them to derive its pure conclusion.

Validation: `python3 tools/lake.py build
MachCSL.Logic.FsDurReadbackLink` passes 479 jobs. The three modules contain
14 named laws. A fresh physical-origin audit checks all 26 declarations
and their transitive types, theorem/opaque bodies (`allowOpaque := true`),
and referenced constructor fields. Only `propext`, `Classical.choice`,
and `Quot.sound` occur; no unsafe or partial semantic dependency, zero
exclusions. The same audit additionally rejects every dependency in
`FsDurSnapshot.Initial`; none occurs. Audit source in the working
environment: `/tmp/xv6-lean-research/FsDurReadbackOwnerAudit.lean`.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

The registry import also exposes initial allocation APIs already present
in the repository; the audited readback theorem cones do not use them.
Runtime source-instance transport and epoch cloning are separate next
obligations. The nearby source `dsnap_step` swap is not claimed by these
reader laws, and full kernel crash refinement is still outstanding.

Coordinator full-source review and independent full-body audit passed; see
`docs/reviews/fs-dur-readback-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
