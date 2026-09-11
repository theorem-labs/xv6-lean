# Native snapshot configuration preparation

Frozen implementation: six Lean modules, nine checked contract fields and
22 named theorems. All native rules reuse existing capacities and names;
no registry extension or Initial constructor is used.

Source baseline: arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

## Source correspondence

- `FsCfgSnapDefs`: source FsCfgSnap section6/9 resource columns and
  SystemAdequacy's own-state preparation. `snapshot` is the existing
  six-leg fsSnap, indexed by canonical recovery. Prepared includes exact
  HeaderWF and recovery facts, native-state Snapshot.OK, logstart equality,
  positive rounded width and 32-bit bound, encoding at that state's own
  home set, the complete header exception set and metadata coverage.
  No pure fact is substituted for native snapshot ownership.
- `FsCfgSnapSpec`: four routing, three read/loan and two allocation
  contracts. Review found an unintended Int inference for three `nib`
  binders; the coordinator approved explicit Nat annotations to match the
  source and design. All source widths now use Nat with explicit signed
  equality. No other signature columns changed.
- `FsCfgSnapReadProofs`: FsCrash2241–2269/2421–2430's durable accessor,
  native P_dur_clone and return through the original wand. The clone is a
  new source-instance transport family, not duplicated ownership. The
  returned loan is opened at its own names/state; functional recovery
  identifies its map, and actual recovered-block fullness justifies native
  readback. HeaderWF is retained from Pfs, not inferred from lend alone.
  SystemAdequacy352–405 supplies the standing `start=2` and log coverage
  seams; superblockOK identifies the state's start and proves the rounded
  width bound. SnapshotCoverage proves metadata coverage without an image
  sweep or an assumed second snapshot state.
- `FsCfgSnapRouteProofs`: exact FsCfgSnap section6 map/domain routing,
  multiplicity/type bridges, region link authorities and directory entry
  tickets. The root's actual spare token is matched by native authority
  agreement and retained in its keep-alive. Section9's top split retains
  live fragments and supplies every rounded-region free top-boot column.
  Local.bareFree proves the exact freeNode equality. Region membership is
  only a subset of the arbitrary finite inode map's domain; extra keys
  are discarded affinely as in source. Tokenless entries, markers and
  malformed total-lookup default are unchanged.
- `FsCfgSnapProofs`: source section9's root-slack allocation derives its
  native validity witness from the held snapshot's readback. The actual
  FsBootRecovery byte mint uses the SAME two allocated link/top names.
  All ten byte-bootstrap columns, fresh top authority, routed inode
  columns, original named snapshot, exact physical-byte complement and
  arbitrary frame are returned. The era wrapper first loans/clones from
  Pfs indexed by `machine.devices.virtio.v_disk`, then uses the existing
  physical byte name from Era.bootClients. It returns Pfs, the full Era
  interpretation and all five other client columns unchanged.
- `FsCfgSnapLink`: all nine laws at the existing registry43 and explicit
  disk-camera/name coherence. No new world or camera is allocated.

The existing frozen LinkBootSpec comment describes epoch-zero use. Exact
FsCfgSnap1000–1007 invokes the same native root-slack link/top allocator
at every era after resource readback. This implementation follows that
source use. It does not call the separately audited Initial snapshot
constructor, and the old comment is not treated as a semantic restriction
on the algebraic theorem. No frozen files were changed to make this work.

## Checked evidence

- `python3 tools/lake.py build MachCSL.Logic.FsCfgSnapLink`: PASS,
  608 jobs; no warnings in new modules. Read proofs ~0.9s, route proofs
  ~1.0s, allocation proofs ~0.9s, concrete Link ~0.7s.
- Fresh physical-origin audit of all six files: **92 declarations**, all
  public/private/generated roots, transitive types, opaque bodies and
  datatype constructors. Standard `propext`, `Classical.choice` and
  `Quot.sound` only; zero exclusions, unsafe/partial dependencies or
  Initial allocation dependencies.
- Reproducible local evidence:
  `/tmp/xv6-lean-research/FsCfgSnapOwnerAudit.lean`,
  `fs-cfg-snap-owner-audit.log`, `fs-cfg-snap-final-build.log`.
- Direct allocator/caller inventory in these six physical modules:
  `P_dur_clone ← loan`;
  `boot_alloc_root_slack ← allocate`;
  `recovered_boot_ghosts ← allocate`;
  `loan ← era_allocate, readSpec`;
  `allocate ← era_allocate, actual`.
  Specification packaging is distinguished from runtime composition.

## Remaining source closure

This is the substantive native preparation/routing core, not the complete
`fs_cfg_alloc_snap` theorem or either full boot kit. Missing source clients
remain: full log/icfg genesis, reference/liveness/stamp/box/off-set columns,
buffer slots, actual inode-block/indirect vocabulary and inode-pool stock,
bitmap invariant allocation, Bio names, allocator/page names, icache IDs
and deposits, and file liveness authority. The fresh top authority remains
explicitly returned; it has not been silently replaced by a top invariant
without the corresponding armed-registry resource.

Physical-extent reindexing and the full crash-invariant accessor are also
separate. This boundary's Pfs already has the actual machine disk as its
index. It does not establish WAL sector-write preservation, complete
kernel boot or whole-system adequacy.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
