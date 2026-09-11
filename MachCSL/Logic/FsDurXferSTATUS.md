# Native filesystem source-instance transport

Frozen bounded port of `iris/FsDurXfer.v` §§4a'–4b, lines1208–1357,
at `arxiv-v1` (`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`). Four modules
provide ten named laws, including the four source allocation/transport
laws and the specification/capacity wrappers.

`fs_footprint_mint` is the exact source pure-fact helper: Shape and
positionwise run disjointness permit allocation of a fresh name at the
existing Disk image camera, initialized to the run union. Its output is
that map authority and a full footprint at the fresh byte name. It does
not assume Snapshot.OK, choose bytes by decoding the state, or allocate
an Iris world. The pure inputs are not linear authorization. Runtime
integration must establish them from the source; this is a source-defined
helper, distinct from the initial-image constructors.

`fs_footprint_xfer` performs that source reading. From the supplied
fractional footprint it extracts the exact existential pool and Shape;
its separation and PhiExcl give run disjointness. PhiAgree with the
provided authority gives inclusion of the source run union in that
authority's byte map. It then invokes the mint and returns the original
authority and footprint unchanged alongside the fresh map authority and
full footprint. The theorem accepts every DFrac whose self-composition is
invalid, preserving Own/OwnDiscard distinctions and not narrowing the
source's fraction contract.

The whole-state transfers require precisely a share strictly greater
than one half. Their byte column uses the byte transfer. Their new link
family is allocated at a choice element read from the SOURCE's own link
resources and native camera validity; the top map is the unchanged source
inode map. The ordinary form returns the source state, fresh byte/map
authorities, all top fragments, and a fresh full state. The spare-token
form additionally returns both the original and the fresh token at the
caller's arbitrary signed inode and inode type. It derives joint native
validity with that token and does not assume root slack as a pure clause.

Concrete wrappers use the current Disk12, FsLink23, and FsTop25 capacities.
Every allocation stays in those existing cameras and the same Iris world.
The source's authority, byte values, inode map, ghost names, fractional
state, and optional token remain in the result. No physical disk is
rewritten and no source ownership is silently replaced.

Validation: `python3 tools/lake.py build
MachCSL.Logic.FsDurXferLink` passes 463 jobs. A fresh physical-origin audit
checks all 32 declarations and their full transitive types, opaque/theorem
bodies (`allowOpaque := true`), and constructor fields. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; no unsafe/partial semantic
dependency, zero exclusions. Explicit rejection of
`FsDurSnapshot.Initial` dependencies passes. No `sorry`, custom axiom,
`native_decide`, or `bv_decide` is used.

The audit also enumerates direct references to `fs_footprint_mint` across
the full imported environment. Exactly two occur: `fs_footprint_xfer`
(the resource-derived source-instance call above), and `mintSpec`
(the generic specification wrapper). `registryMintSpec` references that
wrapper. Later direct consumers must be reviewed for their source-reading
proofs; this audit result does not forbid the source's later collection
consumer or certify an unimplemented caller. Working audit:
`/tmp/xv6-lean-research/FsDurXferOwnerAudit.lean`.

The next separate layer is native Pdur construction off a source instance,
epoch cloning via that transport, and the exact registry-swap update.
No complete commit, reboot, collection invariant, or crash refinement is
claimed by this slice.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
