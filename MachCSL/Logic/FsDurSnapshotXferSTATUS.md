# Native durable snapshot transport and cloning

Frozen bounded port of `iris/FsDurSnap.v` lines854–926 and1368–1380,
at `arxiv-v1` (`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). Four modules
provide seven named laws, including the source transport, clone, registry
step, specification, and concrete capacity wrappers.

`P_dur_alloc_xfer` takes the source's exact inputs: an exclusive byte view,
PhiAgree with its authority map, a filesystem share above one half, the
snapshot's sole pure Shape clause, and inclusion of that authority map
in the target disk flattening. It consumes the authority, fractional
state, and root token as inputs to a basic update, then returns all three
unchanged alongside native Pdur. The new byte map's subset proof is
composed with the caller's supplied inclusion; the state, top map,
fragments, and root token come from native source-instance transport.
There is no Snapshot.OK or full-block premise.

`P_dur_clone` has no additional pure premise. It opens the existing
snapshot, recovers exactly its stored Shape and byte-map inclusion, and
uses its native byte authority as PhiAgree. Transfer at full share
produces the second epoch. The proof reconstructs the first at its exact
original byte, link, and top names with its original authority, fragments,
state, and root token, using explicit conjunct placement. This is fresh
native allocation through source transfer, not duplication of linear
ownership and not a call to an initial-image constructor.

`dsnapStep` is exactly the source basic-update wand from old Pdur to new
Pdur. `dsnap_step_xfer` consumes a supplied next Pdur and returns that
wand; its implementation discards the affine old epoch. It allocates no
name and does not claim the target snapshot can be obtained from a pure
disk value. Concrete wrappers use existing Disk12, FsLink23, and FsTop25
capacities in the same Iris world.

The source's raw ordered flattening definition remains unchanged.
No additional malformed-map correspondence claim is made; the only byte
identity assumption in the generic transfer is precisely the source's
explicit map inclusion. Cloning reads that inclusion from the existing
native snapshot itself.

Validation: `python3 tools/lake.py build
MachCSL.Logic.FsDurSnapshotXferLink` passes 475 jobs. A fresh physical-origin
audit checks all 17 declarations and their full transitive types,
opaque/theorem bodies (`allowOpaque := true`), and constructor fields.
Only `propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe or
partial semantic dependency, zero exclusions. Explicit rejection of
`FsDurSnapshot.Initial` dependencies passes. No `sorry`, custom axiom,
`native_decide`, or `bv_decide` is used.

A full imported-environment scan finds the same two direct references to
`FsDurXfer.fs_footprint_mint`: `FsDurXfer.fs_footprint_xfer`, which derives
its premises from source resources, and the generic `FsDurXfer.mintSpec`
wrapper. This layer adds no direct mint call. Working audit:
`/tmp/xv6-lean-research/FsDurSnapshotXferOwnerAudit.lean`.

Home-coverage readings, logged-era installation wrappers, collection,
WAL integration, and the full crash/boot protocol remain subsequent
source dependencies. This slice does not establish a complete commit or
reboot theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
