# Native top inode camera

Frozen generic camera layer: `Xv6Cameras.v:508–513`'s `fsTopG` and
`FsState.v:234–271`'s top fragments at xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, with the native GhostMap operations
used by the source boot allocators and inode retagging.

The value type is **exactly `Xv6.Fs.DurableNode.Node`**, retaining the complete
record, indirect entry list, and sparse held-block map. `auth` and
`allFragments` accept the existing `DurableState.InodeMap` directly. The
camera is native `HeapView Int (Agree (DiscreteO Node))` over the same
`Std.ExtTreeMap Int` finite-map family. No replacement node, encoding,
well-formedness filter, missing-key default, or new snapshot predicate is
introduced. Arbitrary malformed and free nodes can be stored or freshly
allocated, as required by the source camera.

`FsTopDefs` separates the uninitialized capacity from runtime names. `fragQ`
supports all `DFrac` values, `frag` is its full-share form, and the source
`topFragQ`/`topFrag` wrappers read the exact `FsView.View.top` name.
`gammaQ` leaves this ghost column unchanged. `authQ` additionally exposes the
underlying native fractional authority; source `auth` uses `.own 1`.

`FsTopProofs` supplies timelessness, authoritative lookup and map agreement,
fragment agreement and fraction validity, split/rejoin, the three-quarter
and quarter split, and full-fragment exclusion. Updates require both the
full authority and the full old fragment. `update_frame` preserves an
arbitrary separate resource; `update_other` records that the resulting
finite map retains every other key. Fresh insertion requires key absence.
`allocate` uses native `ghost_map_alloc` and returns a fresh runtime name,
full authority, and all per-key full fragments for an arbitrary input map.
No pure image-validity premise is needed. `actual` constructs every field
of `FsTopSpec` from these checked proofs.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsTopProofs` passes
227 jobs; the proof module takes about 0.8 seconds. A fresh physical-origin
audit checks all **68 declarations** in the three modules, including their
transitive types, bodies, and referenced constructor fields. Only
`propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe/partial
semantic dependency and zero excluded declarations. The audit source is
retained at `/tmp/xv6-lean-research/FsTopOwnerAudit.lean` in the working
environment. No `sorry`, custom axiom, `native_decide`, or `bv_decide` is
used. Independent generic-layer review passed; see
`docs/reviews/fs-top-review.md`.

`FsTopLink` now extends the actual `Lock.registry` at slot **25**, after
its exact source lock product at slot **24** and the link camera at 23.
It preserves the earlier indices and exposes explicit capacities for all
existing machine, heap, era, observation, UART, link, lock, and invariant
resources, including an actual `InvGS` constructor. The top camera still
uses arbitrary source nodes without a validity filter. No existing
registry file was changed.

The combined `FsTopLink` build passes 399 jobs. A fresh physical-origin
audit of the four new Lock modules and `FsTopLink` checks all 194
declarations with only the standard three axioms, no unsafe/partial
semantic dependency, and zero exclusions. See `LockSTATUS.md` for the
source mapping and audit command. Independent registry review is pending.
Source `lockG` also includes a separate sleeplock holder/count camera;
slot 26 is only proposed for its future implementation, with no
placeholder camera or full source `lockG` instance claimed.

Next native dependencies remain the nested inode/link/bitmap/filesystem
resource bundles, combined top/link allocation (including the source spare
root token), block-byte flattening and carving, and actual `fs_snap`/`P_dur`
allocation and transport. This camera alone is neither `P_dur` nor a
substitute for that resource.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
