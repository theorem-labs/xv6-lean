# Native filesystem crash record, custody and receipts

Next boundary after actual-disk FsBootRecovery. The purpose is to connect
the recovered committed map to the existing native durable snapshot, so
bootstrap can obtain HeaderWF and Snapshot.OK from source crash resources.
Neither is introduced as a substitute pure premise for the final rule.

Source baseline is arxiv-v1 fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.
Read contracts: RiscvPtsto171–173/411, Xv6Cameras463–478,
FsCrash503–514/1494–1523/1666–1843/1845–1967/1984–2050/
2130–2275/2503–2540, WpLock249–260. Exact native MonoList algebra is
available in Iris.Algebra.Lib.MonoList; existing registry15, monoNat3,
Lock24 and Disk12/Link23/Top25 capacities cover the other resources.

The coordinator reserved slots 42 (history) and 43 (mirror) for this
boundary. No slot implementation is included in this design. Both cameras
are required by the source; neither is replaced by an abstract predicate.

## Data and actual resources

Proposed owned prefix: `MachCSL/Logic/FsCrash{Defs,Spec,HistoryProofs,
ArmProofs,Proofs,Link}.lean`, with extra pure proof module if useful and
FsCrashSTATUS. Definitions and Spec will be checked and submitted before
native proofs. No existing module or umbrella changes.

- `Record` has exactly `committed : BlockMap` and `history : List BlockMap`.
  It carries no physical disk field. `RecordWF r physical cov ls` is exactly
  recovery to r.committed, history.getLast? = some r.committed, and HeaderWF.
  Its nonempty-history consequence is proved. No Snapshot.OK is stored here.
- `LogMirror` is the source single-field record `view : Int → List Byte`.
  Arbitrary functions, negative keys and malformed byte lengths remain
  legal values. `MirrorOK mirror physical cov ls` is equality only on
  `cov ∪ logRegion ls`, not on the whole infinite view. `mirrorOf` and
  pointwise update are the source constructors.
- `Names` contains exactly history, swap, registry and started GNames.
  These stay explicit parameters, avoiding a circular fixed crash instance.
- History camera is native `MonoList (DiscreteO BlockMap)`, with full
  authority and persistent prefix lower bounds. A receipt for D is exactly
  `∃ prefix, historyLowerBound (prefix ++ [D])`; it owns no disk bytes.
- Mirror camera is native `GhostVarG GF LogMirror`. Custody uses exactly
  half at the named Era.Record.logMirror. Agreement and updates use both
  actual native halves, never a pure assumed mirror or authoritative map.
- `bootToken g := Lock.frag lockCapacity g none`, retaining its existential
  acquisition position. It reuses the full source product camera at 24;
  allocation/exclusivity/Timeless do not imply an acquired spinlock.

Capacity carries the two new native capacities plus explicit existing
Era registry, monoNat, Lock, Disk, FsLink and FsTop capacities. The concrete
registry extends existing registry41 at 42/43, preserves every earlier
entry and all entries 44+, exports coherent existing capacities needed by
FsBootRecovery and full native InvGS. Disk12 is shared structurally by the
snapshot and physical bootstrap; source ghost names remain independent.

## Exact generation custody and native updates

`registered names g era` is the existing discarded registry15 fragment.
`started names g` is the native monoNat lower bound g+1 at names.started.
`custody names cov ls disk g` is exactly an existential era and LogMirror
with those two persistent receipts, its actual half mirror token, and
MirrorOK of that mirror against blocks disk.

`arm names cov ls disk` is an existential c with full monoNat authority
at names.swap and the source disjunction: c=0, or an existential g with
c=g+1 and custody at g. The at-rest arm has no mirror ownership. It is not
an unrestricted authority over any era or a weakened pure generation test.

Native laws preserve exact source inputs:

1. at-rest construction consumes the supplied swap authority at zero;
2. custody_started duplicates only the persistent started receipt;
3. arm_le requires started authority n and explicit n=g+1, preserves the
   authority and original arm branch, and derives c≤g+1;
4. arm_swap takes separate old/new disk images, n=g+1, MirrorOK of the
   supplied new mirror at the NEW disk, the selected registered/started
   receipts, started authority, a half of that era's mirror, and the old
   arm. It returns the arm at the new disk, the same started authority and
   persistent swap lower bound g+1. Old custody is abandoned affinely, as
   in source; there is no revocation or forced mirror-name equality with
   an obsolete era;
5. arm_accessor takes registered g/era, swap lower bound g+1, started
   authority n=g+1, this era's mirror half M0 and the current arm. Upper
   and lower bounds squeeze the held custody generation to g. Registry
   agreement then identifies the complete era, and mirror agreement gives
   MirrorOK M0. The rule returns the started authority and a continuation
   accepting any disk'/M' with proved MirrorOK, performing an actual
   two-half update and returning both the new arm and caller mirror half.

The accessor's continuation is the source abstraction over a separately
proved disk landing. It does not prove arbitrary hardware writes preserve
recovery. It cannot be used without the registry/swap/start/mirror resources
that identify the currently held era.

## P_fs, readback and supplied-snapshot construction

`Pfs names cov ls disk` is exactly:

```
∃ r, historyAuth names.history r.history
   ∗ pure (RecordWF r (blocks disk) cov ls)
   ∗ arm names cov ls disk
   ∗ FsDurSnapshot.Pdur diskCapacity linkCapacity topCapacity r.committed
```

`named swap registry started` existentially packages Names with the three
source seam equalities. No fixed durable-view ghost name is added. A
separate source `lend cov ls disk` definition is recovery plus a whole
native Pdur instance; an accessor is not mislabeled as permanently lending
a duplicated snapshot.

Public laws:

- honest history allocation, snapshot, prefix validity and monotone update,
  plus persistent receipts;
- `recovers`: recovered current committed state is the last member of a
  nonempty history;
- `receipt_committed`: any held receipt names a member of that history;
- `header_keep`: extract exact HeaderWF and return the same Pfs;
- `commit_receipt`: recover D and derive an existential Snapshot.OK state D
  by the existing native Pdur readback, with BlocksFull DERIVED from the
  record's actual recovery; return the same Pfs;
- `bank`: additionally return the persistent current receipt and exact
  Snapshot.Holds D, preserving Pfs;
- `durable_accessor`: expose recovery and the existing Pdur D with a wand
  returning it to the same crash predicate; no fresh allocation;
- `of_durable`: from source recovery/HeaderWF, PROVIDED native Pdur D,
  PROVIDED swap authority at zero and arbitrary frame, allocate only the
  history singleton and package source Pfs plus its first receipt and the
  three seam equalities. This is the resource-consuming core of
  P_fs_alloc. It does not require a pure Snapshot.OK, call an Initial
  constructor, or discard/replace physical disk authority. A later exact
  wrapper can accept the source update-producing Pdur premise by composing
  it outside this constructor.

A final generic caller combines Pfs indexed by the ACTUAL
state.devices.virtio.v_disk with the already supplied Era.interp and
Era.bootClients. It derives HeaderWF, invokes FsBootRecovery, and returns
Pfs, the original full Era.interp, every other client leg, all bootstrap
outputs, exact physical-byte remainder and frame. CovIn remains the source
geometry premise. It may also expose the derived Snapshot.OK through the
non-destructive readback. This removes the previous generic HeaderWF
input without substituting a pure recovery or snapshot oracle.

## Limits and subsequent source closure

The new predicate is the exact runtime consistency resource that source
crash-preservation rules maintain. This boundary does not prove every WAL
sector write preserves it. The physical-byte `P_fs_named` extent agreement,
write permits, torn-sector/replay invariants and banking at actual DMA
landings remain subsequent source work; the current generic Pfs index is
explicitly the current machine disk at the bootstrap call.

No literal Initial producer is added to these modules. Connecting the
already checked initial Pdur producer to `of_durable` will be a separate
leaf with the repository's Initial callgraph audit updated only by the
coordinator. Complete FsCfgSnap configuration allocation then uses the
source durable accessor/transport path to build era-local inode resources
from this actual committed map. It must retain the snapshot return path
and all separate link/top/custody ownership; no assumed Snapshot.OK can
stand in for that native transport.

Validation will build each module and audit all physical-origin roots,
opaque bodies, types and datatype constructors; only the standard three
foundational axioms, no exclusions, unsafe/partial or Initial allocator
cone. Public theorem source mapping and direct allocation callers will be
recorded in STATUS before freezing the boundary.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
