# Native inode-region prelude peer review

Decision: pass for the declared allocation/decoding prelude. The coordinator read all ten modules, source Xv6Cameras.iregG, InodeRegion.imark/ireg_out/ireg_couple/ireg_recs, and IcacheBoot's decode and initial-map/allocation sections at the paper pin. The coordinator requested separation of operational definitions from proofs; the final version moves these into CodecDefs and BytesDefs without changing theorem statements or proofs.

The camera is the source signed-key native ghost map over Dinode values. It supports actual fractional record ownership and full-authority updates. Marker keys are exactly -(i+1), with existential marker contents; initial markers use the empty-address zero record. Finite domain, key injectivity, nonnegative/negative disjointness and left-biased map union are proved. The source 32-bit region bound justifies conversion of every inode number. Allocation returns both original fragment families and the caller's unchanged frame in the same Iris world.

Every full 1024-byte block decodes through sixteen exact 64-byte records, with kernel-checked encode/decode roundtrip and thirteen-address well-formedness. Native record rows factor the same supplied block ownership in both directions. bootstrap_prelude preserves the source's explicit decoded-image property premise, derives an actual decoded list, and returns its six properties, the fresh record authority/cells and the same supplied bytes as record rows. It does not assume an initialized slot, abstract invariant or physical disk reset.

The concrete registry extends the held-lock world at slot 27 and proves preservation of slots 0–26 and 28 onward. Explicit native capacities connect the existing byte, timestamp, heap-metadata, register, device, disk, invariant, observation, link, top and lock cameras. It allocates no second Iris world and calls no initial-only durable snapshot constructor.

Fresh coordinator audit covers all 217 physical logical declarations, including private helpers, types, opaque bodies and referenced constructor types. Only the standard three axioms occur, with no unsafe/partial or FsDurSnapshot.Initial dependency. The sole excluded root is the generated total-recursion companion decodeRecords._unsafe_rec; the logical decoder and its whole cone are checked. Evidence: /tmp/xv6-lean-research/FsInodeRegionPeerAudit.lean and fs-inode-region-peer-audit.log. Final component build: 465 jobs.

The full ireg_alloc still needs the source reference/count/freeze/shield resources, observation receipts, link/top rows, escrow registry, boot shelter and actual slot/invariant construction. The prelude does not replace any of them with a callback. Its generic fresh record allocation is source resource construction, not a new physical filesystem or a runtime use of the initial snapshot allocator.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
