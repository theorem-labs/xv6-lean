# Native filesystem assembly from the provided footprint

Frozen source slice: `FsDurAlloc.v:803–917` (domain regrouping and
`fs_state_of_ledger`) at xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The four modules reuse the exact arbitrary durable state, six-slot
footprint, and existing native `FsState.state` hierarchy. `remainderMap`
is only the explicit difference between a supplied whole byte map and
the selected slot union; it creates no new state carrier or ghost name.
`AssemblySpec` states the full-slot conversion, full-block assembly,
and its provided-byte-image generalization, each retaining the exact
complement and caller frame where applicable.

`keys_map` proves the native finite separating conjunction over keys
matches the same map's key-only conjunction. `slots_grouped` uses this
bridge for all inode records, all owned data slots, and all indirect
roles. No inode or stored block is filtered by file size, type, or
nonemptiness. Record conversion discharges the source modulo-32-bit
address equivalence using `Snapshot.Bytes.inum`. Data and indirect
resources recover their exact full-block clauses from the existing
snapshot block reads. The free pool retains signed count semantics and
block zero; its clear bits receive the same supplied block bytes under
the source existential, while used slots contribute the empty resource.

`slots_to_footprint` assembles the complete native byte column.
`state_of_slots` combines it with the supplied link column at the same
view name, using the already-proved `FsState.state_split` and
`FsState.ghost_split`. It derives the pure parse, local-inode, and geometry
clauses from exactly `Snapshot.OK`; those pure facts do not replace any
native byte or link ownership. Top-map fragments remain outside the
filesystem state exactly as in the source.

`state_of_blocks` consumes a full block ledger and the existing native
link family and returns `FsState.state` beside the exact flattened-byte
complement and frame. `state_of_image` accepts a larger provided byte
map with `flatten disk` as a submap, and returns the complement relative
to that larger map. These generic rules allocate no ghost resource and
preserve both view names and the caller's capacity. An original disk
authority can remain in the arbitrary frame unchanged. All three fields
of `AssemblySpec` have actual proofs.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsDurAssembleProofs`
passes **445 jobs**. There are **13 named theorems**. A fresh physical-origin
audit checks all **27 declarations** in the four modules and all transitive
types, bodies, and referenced constructor fields. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed, with no unsafe/partial
semantic dependencies and zero exclusions. Audit source:
`/tmp/xv6-lean-research/FsDurAssembleOwnerAudit.lean` in the working environment.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

Native `fs_snap`/`P_dur` definitions and epoch-zero allocation are the
next separate source dependency and are not claimed by this assembly
checkpoint. No fresh allocation has been substituted for supplied
runtime resources, and no new Iris world is allocated.

Coordinator full-file/source review and a fresh independent full-cone audit passed;
see `docs/reviews/fs-dur-assemble-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
