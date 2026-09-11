# Native filesystem resource hierarchy

Frozen native definition and bounded proof checkpoint for xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`FsStateInodeDefs` maps `FsStateInode.v:439–480,685–744,806–826,
1011–1042,1090–1099` to native resources. Record bytes use the exact
32-bit wrapped inode index; the separate `recOwnedAt(Q)` form uses signed
division and remainder. The two forms agree under the source
`0 ≤ i < 2^32` premise. No address-list well-formedness condition is hidden
in the record resource. Indirect ownership is empty exactly when its
address is zero; otherwise it owns the entire encoded block. Data
ownership iterates the complete stored block map, including allocations
beyond EOF and arbitrary malformed nodes. The existing full-block
predicate enforces 1024 bytes at every held block.

Directory token resources retain the exact `LinkFamily.tokenless` formula,
guarded parent equality, existential value and marker set, marker-domain
conditions, and exact deposit-time link count. `inodeGhost` holds native
link authority, entry tokens, and the existing 16-clause inode-local
predicate. It contains no top-map fragment. `inodeOwned` pairs that ghost
column with the record, data, and indirect byte legs.

`FsStateBitmapDefs` maps `FsStateBitmap.v:41–65`: a used block contributes
`emp`; each free slot contributes an existential arbitrary full block. The
pool is the exact signed `seqZ 0 nb`, empty when `nb < 0`, and includes
block zero when the range does. `freePoolBut` retains the source list
position hole. Bitmap ownership includes all 1024 encoded bytes, with no
extra padding or used-set validity assumption.

`FsStateDefs` maps `FsState.v:169–212,300–323,420–429,486–490`.
Superblock ownership is full-block ownership plus the exact parse.
`fsInodes` ranges over the complete arbitrary map, including free records
in the rounded inode region. `state` fixes only the byte column to its
`DFrac`; the link resources remain whole. Its final pure conjunct is the
existing source `DurableState.Geometry`, including exact region coverage
and directory conditions. `footprint`, `ghost`, `pureState`, `linkNode`,
and `links` preserve the source nested shapes and existentials. Top-map
fragments remain separate resources in the later snapshot/escrow layer.

The three proof modules establish **37 named laws**, plus timelessness
instances throughout the hierarchy. They include the exact signed/wrapped
record bridge with its range premise, full/share aliases, indirect and
whole data-leg fractional split, selected stored-block access and
reassembly, inode local projection, signed pool lookup and held-out-slot
split, and the source `free_pool_used_q` consequence of actual byte
exclusion. The whole-state proofs provide geometry projection, inode
focus/reassembly preserving the other native resources, share/name
independence, and the exact `state ⊣⊢ footprint ∗ ghost` factoring.
`actual` constructs all five fields of `ResourceSpec` from these proofs.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsStateProofs`
passes **237 jobs**. Each proof module elaborates in about 0.8 seconds.
A fresh physical-origin audit covers all **130 declarations** in the
seven new modules, including all transitive types, bodies, and referenced
constructor fields. Only `propext`, `Classical.choice`, and `Quot.sound`
occur; no unsafe/partial semantic dependencies and zero exclusions.
The audit source is retained at
`/tmp/xv6-lean-research/FsStateOwnerAudit.lean` in the working environment.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.
Root source review of the four definition/interface modules passed;
independent root review of the complete proof checkpoint passed; see
`docs/reviews/fs-state-review.md`. A fresh separate 130-declaration
dependency audit also passed with standard axioms only.

The remaining source APIs include free-pool take/give and allocation,
whole-footprint shedding, inode/link packing and gathering, native
link-family validity and allocation, and byte flattening and footprint
carving. These are separate subsequent proofs, not assumed fields of
`ResourceSpec`. In particular, no durable `fs_snap`/`P_dur` allocation or
transport is claimed. The pure snapshot predicate remains separate from
these native resources.

The existing `FsLink.Capacity` is explicit; no registry or camera is added
by this hierarchy. Full filesystem allocation will also need the separate
existing FsTop capacity and the same Disk byte camera. No umbrella edits
are included in this checkpoint.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
