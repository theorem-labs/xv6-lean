# Native shared KPT ghost algebra

The five-module KPT ghost slice is implemented and linked.
`KptGhost.nativeSpec` discharges all 18 contracts for supplied coherent
capacity witnesses; `KptGhost.registrySpec` discharges them at the explicit
48-slot family. This is ghost algebra, not physical translation correctness.

The mapping carrier is native `GhostMapG` on finite `ExtTreeMap` keys
`BitVec 27`, with values `BitVec 44 × KptLeaf.Permission`. The permission
carrier has exactly the source RX/RW alternatives. `mapAuth` is bare full
authority; `mapAt` is the source discarded persistent fragment. `allClaims`
is the finite separating conjunction for an arbitrary supplied map. No
physical mapping, static-map inclusion or map well-formedness condition is
hidden in the authority.

`map_lookup` and `map_agree` derive lookup and uniqueness from the actual
native camera. `map_insert` requires an absent key and returns the new
authority and discarded claim together under one basic update.
`allocate_map` first uses native `ghost_map_alloc`, then persists all returned
fragments with `ghost_map_elem_persist` and the native finite-map update law.
This includes the empty-map case and preserves the caller's arbitrary frame.
`claim_lookup` extracts a claim from the real finite separating conjunction.
No static classifier is guessed or assumed.

The tree and publication-bound carriers are separate native non-unital
`Csum (Excl Unit) (Agree (DiscreteO ...))` cameras. Tree snapshots contain
`PtTree.canon t`, never the current raw tree. `shoot`, `agree`, `canonical`,
and the pending-token exclusion/allocation laws use native `iOwn` validity
and frame-preserving updates. `snapshot_set_leaf` composes the proved pure
A/D canonicalization law: it rewrites the snapshot without updating its ghost
name. It assumes the pure mapped path; it does not authorize a physical write.

A bound contains agreement on the exact natural number and the existing
`Tso.Views.llb` receipt, including its pure zero branch. `shoot_bound` must be
paid that receipt; `bound_log` returns it. `bound_agree` compares agreement
payloads even when supplied log names differ, without identifying those log
names. `bound_valid` additionally requires actual authority at the same log
name and capacity to derive B ≤ n. Agreement alone implies no such bound.
Snapshots, bounds, mapping claims and claim bundles are proved persistent
and timeless; the exclusive pending assertions are timeless. Explicit frame
laws cover map insertion and both one-shot transitions.

`allocate` constructs all three actual ghost-resource bundles at fresh
allocated names, preserves the arbitrary frame, and records equality with
the caller-supplied log name. It allocates no log-length authority and does
not retrofit resources into preselected era names. `Names.ofEra` projects
the existing map, tree, bound and log-length fields from the full era record;
name projections themselves imply no ownership. `kptN` is the exact source
namespace `nroot .@ "kpt"`, without an installed invariant.

The registry extends the frozen `SupervisorBits.registry` at map/tree/bound
slots 45/46/47. `registry_old` proves every slot below 45 unchanged;
`preserveOld` transports any such supplied `ElemG` witness, including unnamed
client capacities. Every named predecessor capacity and shared-slot identity
is explicitly reconstructed, including filesystem/crash, machine/era,
UART/devices, native invariant slots 16–19 and supervisor bit slot 44.
`kptCapacity.views` is definitionally the machine era's original Views
capacity; its view/mono indices remain 2/3. There is no duplicate log camera,
new era field, or second native invariant world. `registry_unused` preserves
all slots at 48 and above.

Source map (paper pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`):

- `RiscvPtsto.v:112–120,1157–1182`: exact tree/bound cameras and mapping claims.
- Complete `KptGhost.v`: pending tokens, canonical snapshots, receipt-bearing
  bound, shoot/agreement/rewrite/allocation laws and namespace.
- `KMap.v`: bare map authority, lookup, fresh persisted insertion and generic
  claim-bundle extraction. Concrete `kmap_M0`, its classifier and physical/
  virtual ownership bridges remain separate.
- `PtTree.v:1930–1953`: canonical tree preservation used by
  `snapshot_set_leaf` through the proved native `PtTree` contract.

Recursive tiered tree ownership, shared invariant publication, boot
context-to-pin conversion, per-event invariant accessors, generalized raw
pointer walking, TLB coherence and translated `mycpu` remain subsequent work.
No current physical tree is inferred from map authority or a canonical
snapshot. The implementation does not claim a full `KMap.v` port or native
translation/function correctness.

Validation:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.KptGhostLink`
  passed all 600 jobs (proof module 1.2 s, link module 912 ms).
- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/KptGhostOwnerAudit.lean`
  checks every physical declaration in all five modules, including private
  declarations, complete types, opaque bodies (`allowOpaque := true`) and
  inductive constructors. All 353 physical declarations passed with only
  `propext`, `Classical.choice`, and `Quot.sound`, zero exclusions and no
  unsafe/partial dependency. Raw result:
  `/tmp/xv6-lean-research/kpt-ghost-owner-audit.log`.
- `git diff --check` and direct whitespace/final-newline checks cover all
  owned files, including new untracked files.

The compiler-exposed missing parentheses in `mapInsert` were corrected with
coordinator approval before proof completion: both newly minted resources
are under the same update, matching `KMap.kmap_insert`. No extra premise or
weaker source operation was introduced.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
