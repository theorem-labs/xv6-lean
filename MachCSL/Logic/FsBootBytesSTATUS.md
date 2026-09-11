# Supplied disk bytes to filesystem bootstrap

Stage 2 is frozen in eight modules: DiskClientDefs, BioViewDefs,
FsBootBytesDefs/Spec/PureProofs/CarveProofs/Proofs/Link. All six PureSpec
laws, three CarveSpec laws and complete native fs_boot_ghosts contract are
implemented. There are 21 named theorems, including specification instances
and concrete capacity equalities. The definitions and exact contracts
received coordinator source review before implementation.

DiskClient.Names retains all fifteen DiskPtsto fields (img, slot, nc, np,
claim, cfg, ord, nr, stage, head, perm, fl0, fl1, flr, pos). No driver
camera is allocated by this data carrier. BioView retains disk names,
32-bit device, finite signed covered set, both actual native content
predicates, and both Timeless witnesses. The fsView specialization uses
existing mclean/mdirty; its witnesses follow from their actual ghost-map
half ownership. No Bio invariant or abstract buffer-cache oracle is added.

Source FsBoot169–234/332–445 is preserved: CovIn and all five mint premises;
provided physical byte name unchanged; pool blocks with raw physical bytes
and mclean, raw cache and clean dirty authorities, actual fixed-view byte
invariant, full unsealed exception handle, second dirty halves, committed
home blocks, and parked outside-home cache halves. The machinery's dirty
half remains inside each pool block and the other dirty half is returned
separately. The actual native fs_alloc supplies all these resources.

The stronger carve and mint additionally return the exact map difference
of unused supplied bytes and an arbitrary frame. The pure subset theorem
uses signed address bounds from CovIn and actual total disk_read lookup;
raw 1024-byte fullness discharges the existing guarded flatten theorem.
Native provided_image_cut performs the split, and checked map-to-set
conversion preserves every covered physical block. The source affine
carve is exposed separately. No supplied disk authority is minted or
replaced. The current machine's Disk12 capacity equals the bootstrap byte
capacity by a checked equality; the Link reuses registry41 unchanged.

Validation: final `python3 tools/lake.py build
MachCSL.Logic.FsBootBytesLink` passed **517 jobs** with no new warnings.
Pure/Carve/Proofs/Link each elaborate in approximately 1 second. Fresh
physical-origin audit checked **140 logical declarations in all eight
modules**, including private/generated roots, complete opaque bodies,
types and datatype constructors. Standard three axioms only, zero excluded
roots and no unsafe/partial or Initial allocator dependency. Evidence:
`/tmp/xv6-lean-research/FsBootBytesOwnerAudit.lean`,
`fs-boot-bytes-owner-audit.log`, `fs-boot-bytes-build.log`.

Elaboration needed explicit finite-map carrier arguments, the existing
memory vocabulary import, and maxRecDepth 2048 for nested source map
aliases. Resource simplification uses Iris-local unfolding; no proof or
runtime trust boundary was relaxed. No definitions changed after contract
approval. Stage 3 derives the mint premises from exact replay of the current
era disk and preserves its remaining boot clients. Its signature review,
full FsCrash resource predicate and complete Bio invariant are subsequent
work; this checkpoint does not assume or claim those interfaces.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
