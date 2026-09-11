# Native crash record, generation custody and durable readback

Frozen seven modules: Defs/Spec/PureProofs/HistoryProofs/ArmProofs/Proofs/Link.
All nineteen approved contracts are implemented: history/boot-token6,
generation-arm5, Pfs7 and actual-era bootstrap1. There are 76 named theorems
(including 42 concrete registry/spec links) and 20 native persistence or
Timeless instances. Exact design and Defs/Spec received coordinator source
review before native proof implementation.

Source mapping (arxiv-v1 fa7f0a01c4b40489fac8ad303f079c2dfc7a1476):

- RiscvPtsto171–173/411 and FsCrash503–514: full arbitrary LogMirror carrier,
  equality only over covered union log-region blocks, native half ownership.
- FsCrash1494–1523: both fs_rec fields and all three well-formedness clauses;
  nonempty history and last-element decomposition are actual kernel proofs.
- Xv6Cameras463–478, FsCrash1666–1788: four GNames, native MonoList of
  discrete finite BlockMap, full history authority/prefix bounds/receipts,
  actual same-world allocation and monotone update. historyEmbed_prefix
  proves both directions by list mapping and DiscreteO.car projection.
- WpLock249–260/FsCrash1764–1780: boot token is the existing Lock24 fragment
  at none, with its existential position retained. Allocation uses native
  Lock.allocate_free and forgets its extra authority affinely; no other
  resource exists at the fresh name. Exclusivity uses the actual product RA.
- FsCrash1815–1967: discarded registry15 receipt, monoNat3 started receipt,
  real half mirror at Era.logMirror, exact zero-or-custody branch. The swap
  accepts separate old/new disk images, derives the upper bound from the
  started authority, abandons only source old custody and updates the same
  swap counter. The accessor combines swap lower and started upper bounds,
  identifies the generation and complete era by native registry agreement,
  obtains mirror agreement, then updates BOTH held halves. Started
  authority and the updated caller mirror half return exactly as promised.
- FsCrash1984–2021/2130–2275: Pfs has history authority, RecordWF, arm and
  actual existential native Pdur. recovers/receipt_committed are source
  readings; header_keep preserves the original predicate. commit_receipt
  and bank derive BlocksFull from actual recovery before native Pdur
  readback, return Snapshot.OK/Holds and the same Pfs; bank also snapshots
  the actual history bound. durable_accessor exposes the supplied Pdur and
  a wand that reinstalls it, with no clone or allocation.
- FsCrash2503–2540: of_durable is the resource-consuming constructor core.
  It consumes provided Pdur and swap authority at zero and allocates only
  the singleton history, preserving its arbitrary frame. It requires no
  pure Snapshot.OK and calls no Initial producer.

The new actual-era bootstrap theorem derives HeaderWF from the held Pfs
indexed by state.devices.virtio.v_disk, then applies the checked existing
FsBootRecovery rule. The same Pfs, complete Era.interp, five other client
legs, complete byte bootstrap columns, exact unused-byte difference and
frame all return. BootstrapCapacity includes the explicit sameDisk camera
identity; the concrete Link proves both sides equal existing Disk12.

Registry43 installs history at42 and mirror at43, preserving every old
entry0–41 and every unused entry44+. Explicit capacities for the old
machine, invariant, filesystem, lock, escrow and icache components remain
available. The native invariant instance and machine/registry/counter/
byte/link/top/boot identities are checked equalities. No previous registry
is modified and no physical disk authority is reminted.

Validation: final `python3 tools/lake.py build MachCSL.Logic.FsCrashLink`
passed **573 jobs**. History/Arm/Proofs/Link compile in about one second;
there are no warnings in the new modules. Fresh physical-origin audit
checked **373 logical declarations in all seven modules**, including
private/generated roots, complete opaque bodies, types and datatype
constructors. Standard three foundational axioms only, zero excluded roots,
no unsafe/partial or Initial allocator dependency. Evidence:
/tmp/xv6-lean-research/FsCrashOwnerAudit.lean, fs-crash-owner-audit.log,
fs-crash-build.log.

The direct allocation/caller check over all seven physical modules found:

- history_allocate: historySpec and of_durable;
- boot_allocate: historySpec;
- of_durable: actual;
- arm_swap: armSpec;
- bootstrap: bootstrapSpec.

No literal initial caller was added. During elaboration, the map-prefix
roundtrip needed explicit function composition reduction, native own-op
allocation needed an explicit separating split, and registry construction
needed the existing scoped Unit order. These are checked proof/interface
normalizations; no approved definition or resource contract was changed.

Pfs's disk INDEX remains distinct from the source P_fs_named fixed durable
byte-extent ownership. This checkpoint does not claim extent agreement,
sector-preservation/write permits, crash-swap adequacy, or complete
FsCfgSnap configuration initialization. Those source interfaces must
maintain the now-defined native runtime predicate and transport its
existing snapshot into era-local resources. No assumed Snapshot.OK or
Initial mint stands in for that work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
