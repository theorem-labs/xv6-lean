# Native snapshot preparation and filesystem configuration routing

This boundary advances the era's configuration mint from the existing
crash predicate and real physical boot bytes. It does not yet implement
`fs_cfg_alloc_snap`'s complete inode-cache, allocator, buffer-slot and file
kits.

Source baseline: arxiv-v1
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. Read all 1321 lines of
`FsCfgSnap.v`, `FsCrash.v:2241–2269/2383–2465`, and the relevant callers
`SystemAdequacy.v:352–405` and `BootShared.v:1405–1440/1523–1550`.
The coordinator reviews this contract before new implementation files.

Proposed owned files: `MachCSL/Logic/FsCfgSnap{Defs,Spec,RouteProofs,
Proofs,Link}.lean` and `FsCfgSnapSTATUS.md`, with separate proof modules
if elaboration warrants. No existing definitions, registries or umbrellas
are changed. Reuse the actual Disk12, Link23, Top25 and current crash42/43
capacities; do not allocate a new Iris world or call an Initial constructor.

## Loan and identity

The generic `loan` rule takes existing
`FsCrash.Pfs cap names covered start physical` and an arbitrary frame. It
uses the existing durable accessor and source `P_dur_clone`, gives the
original instance back through its wand, and returns the same Pfs, frame,
and a whole native `FsCrash.lend` resource, together with HeaderWF
read from the same Pfs record. It works at arbitrary signed
`start`; it proves no configuration equality merely from that index.

The `open_loan` rule opens that resource's own existential names and state:

```
lend covered start physical
  ⊢ ∃ g gl gt S,
      pure (Snapshot.OK S (Recovery.recover (blocks physical) covered start))
    ∗ fsSnap (snapGamma g gl gt) g
        (Recovery.recover (blocks physical) covered start) S
```

The map is identified by recovery's functional equality. BlocksFull is
derived from actual recovery, and Snapshot.OK is read from this native
instance while returning it. No existential pure witness is chosen in
place of the instance's own state, and no determinacy theorem about abstract
states is assumed.

A source configuration preparation rule retains that HeaderWF receipt
from Pfs (lend alone does not imply it) and additionally takes the standing
source premises `start = 2` and `logRegion start ⊆ covered`, plus CovIn
when physical bytes are consumed. Snapshot.Bytes.superblockOK proves
`S.superblock.logstart = 2`; that is what reconciles the two starts.
It derives the positive rounded width
`nib = (S.superblock.ninodes / 16 + 1).toNat`, its exact signed equality,
and `16*nib ≤ 2^32`. The committed total view uses the existing raw fallback
outside the recovered map. Full lengths, restrict equality, HeaderWF,
header write-set inclusion, exclusion of block1, agreement outside that
set, and the metadata window are derived from native readback, actual
recovery facts and these exact source geometry premises. No whole-map
configuration equality follows from Pfs alone at arbitrary start.

## Exact link and top routing

Port `FsCfgSnap.v` section6 using existing SnapshotConfig total node lookup,
including its malformed empty-address default and arbitrary finite-map
keys outside the rounded region. The source laws are:

- finite map separation equals separation over its domain at total lookup;
- the full links family restricts to all rounded-region nodes using
  Snapshot.Bytes.regionDomain;
- with the root's actual extra token, split each region node's native
  link authority into `IcacheInodeCustody.ireg_lnk` and its exact directory
  entry tickets; root token agreement is proved from native authority,
  not assumed, and the token remains parked in the root's keep-alive;
- split top fragments into the exact live subset and the complete region's
  `ireg_top_boot` column. Free nodes use Local.bareFree and the checked
  source `freeNode` equality; live positions require no fabricated fragment
  in their boot column. Extra map keys may be abandoned affinely, as in
  source, without strengthening region-domain containment to equality.

The predicates use the existing FsView/FsBlocks names and actual
LinkFamily ticket vocabulary; there is no alternate top map or marker
encoding.

## Allocation from the native source instance

A native configuration-core rule starts with the named fsSnap above and
provided disk bytes at the existing physical name and the HeaderWF
receipt already derived from Pfs. Its generic named-snapshot form keeps
HeaderWF explicit, exactly as the source caller does. It reads the exact
root-slack validity existential from Snapshot.Bytes.links, calls the
existing native root-slack link/top allocation, and calls FsBootRecovery
with those same two fresh names. It returns:

- the original named snapshot and its derived pure facts;
- all existing FsBootRecovery outputs with the same link/top name ties,
  raw physical cache/pool, fixed committed view, complete dirty halves,
  full unsealed exception handle and parked outside-home cache rows;
- the newly allocated top authority, live top fragments, free top-boot
  column, region link authorities including root keep-alive, and exact
  directory entry tickets;
- the exact unused physical-byte remainder and arbitrary frame.

An era wrapper consumes the actual Era boot clients and derives its disk
value from `state.devices.virtio.v_disk`. It returns the unchanged full
Era interpretation, all five other client columns and Pfs. It does not
replace physical disk authority. When a top invariant is later allocated,
its same-name empty armed registry remains a real supplied or allocated
resource, never an assumed invariant premise.

The existing `LinkBootSpec` comment describes initial epoch-zero setup,
but the exact source `FsCfgSnap.v:1000–1007` uses
`fs_boot_alloc_root_slack` at every era after native snapshot readback.
This rule invokes that source algebraic allocator with validity derived
from the held instance. It does not invoke `FsDurSnapshot.InitialSpec` or
reconstruct an arbitrary runtime snapshot from a pure fact. Any comment
correction in frozen files is a separate coordinator-reviewed change.

## Remaining configuration dependencies

The complete source mint still requires the actual log genesis resource,
full icfg allocation (reference/liveness/stamp/box/key/off-set columns),
buffer-slot ownership, inode-pool row predicates and stock allocation,
physical inode block/indirect vocabulary, bitmap invariant allocation,
Bio names, allocator/page names, icache IDs/deposit resources and file
liveness authority. Existing generic region invariants do not substitute
for these missing clients. No complete fs_kit_icache/fs_kit_fsinit_ghost,
`fs_cfg_alloc_snap`, crash invariant accessor, disk-extent reindexing or
whole-system boot theorem is claimed by this boundary.

Build every new module. Audit all physical-origin declarations, including
private and generated declarations, opaque bodies, types and datatype
constructors; allow only the standard three foundational axioms and no
exclusions. Check that all dependencies avoid Initial constructors, and
record direct clone/root-slack/byte-mint callers. Preserve the exact source
contracts and same-name ownership throughout.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
