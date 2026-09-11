# Native durable snapshot and initial allocation

Frozen source slice: `FsDurSnap.v:577–585,807–830` and
`FsDurAlloc.v:933–1010` at xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The five modules implement the native `fs_snap` and `P_dur` resource
predicates over the existing capacities and arbitrary durable state.
`fsSnap` has exactly the six source legs: the snapshot byte authority's
existential submap tie; full top-inode map authority; every full top
fragment; native full `FsState.state`; an existentially typed root-1
keep-alive ticket; and pure `Snapshot.Shape`. Shape has exactly the
source's single domain-below condition despite the older multi-field
source commentary. No `Snapshot.OK` conjunct is added to this resource.
`Pdur` existentially binds three independent names and the complete
state, using the same disk camera for the snapshot view's byte name.

The generic proof module supplies native Timeless instances, component
unfold/reassembly, state/identity/top/root/shape projections, and
existential introduction. These are resource entailments, not aliases
of pure snapshot validity. The arbitrary raw predicate inherits the
explicit flattening qualification from `FsDurBytesSTATUS.md`: comparison
with Rocq's finite-map enumeration is proved on at-most-1024-byte blocks.
No cross-language equality of arbitrary malformed oversized folds or
predicates depending on them is claimed. Initial allocation discharges
the guard using `Snapshot.OK`'s full-block condition.

`Initial.snap_bytes_alloc` allocates a fresh name in the existing native
Disk image camera. `Initial.fs_snap_alloc` then allocates the combined
link family and root-slack ticket using the snapshot's already-proved
native camera validity, allocates the top map and fragments, and spends
the fresh byte ledger and link family through the checked assembly.
It returns all three names and the six-leg snapshot, the exact uncarved
snapshot-byte remainder, and an arbitrary caller frame. Its authorized
byte submap witness is the complete flattening with reflexive inclusion.
`Initial.P_dur_alloc` hides the names/state and may discard that remainder
affinely, matching the source result; the stronger constructor retains it.

These are ordinary native Iris allocation rules designated for initial
epoch setup. The `Initial` namespace and documentation do **not** enforce
once-only use or provide a linear epoch-zero permission. A caller could
apply a pure-input allocation theorem elsewhere; the machine integration
and source-closure audit must restrict this constructor to the initial
producer. Runtime commit and reboot require the separate source-instance
transfer path, which is not supplied here. No epoch transport is claimed.

The actual registry link checks Disk slot 12, link slot 23, and top slot
25. It proves both physical-disk and explicit finite-map authorities
survive initial snapshot allocation unchanged, beside an arbitrary frame.
No existing authority or runtime name is replaced and no Iris world is
allocated. These framing laws alone do not assert equality between an
arbitrary framed physical disk and the supplied snapshot block map; the
concrete initial-image tie remains the next separate leaf.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsDurSnapshotLink`
passes **463 jobs**. There are **18 named theorems**, plus three native
Timeless instances. A fresh physical-origin audit checks all **41 declarations** in the five modules
and their transitive types, bodies, and referenced constructor fields.
Only `propext`, `Classical.choice`, and `Quot.sound` occur, with no unsafe
or partial semantic dependency and zero exclusions. Audit source:
`/tmp/xv6-lean-research/FsDurSnapshotOwnerAudit.lean` in the working environment.
Two additional notation-free type checks confirm that the durable result,
preserved authority, and frame are all inside the returned basic update;
source: `/tmp/xv6-lean-research/SnapshotModalScopeCheck.lean`.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.

The reviewed modal statements place the durable result and returned frame
inside the basic update. The literal initial-image caller is a separate leaf.

Coordinator full-file/source review and a fresh independent full-cone audit passed;
see `docs/reviews/fs-dur-snapshot-review.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
