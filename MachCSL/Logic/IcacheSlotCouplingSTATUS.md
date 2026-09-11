# Inode-slot reference and freeze-mirror coupling

The five `IcacheSlotCoupling{Defs,Spec,PureProofs,Proofs,Link}` modules port the
pure predicates and two native resource columns used by pinned
`InodeRegion.v`. They use the existing per-inum reference ledger and separate
count/mirror cameras, with supplied names and capacities. No registry or
camera is added, and no resource allocation occurs in this layer.

## Source mapping

| Pinned source | Lean definitions and laws |
| --- | --- |
| `InodeRegion.v:435–452` | `fresh_shape`, exact type/size/13-address/nlink conditions; record well-formedness and nlink projection |
| `555–587` | `ireg_claim_ok`, none/shape/off/type projections; raw invalid claim rejected |
| `671–808` | `ireg_ref_ok`, both counter bounds, zero/allocated/unclaimed projections, retire/unclaim/type stability, claim mint, flavored reference mint/spend |
| `860–994` | `ireg_frzm_ok`, `ireg_frz_ok`, exact off/pre/post and raw absent/invalid cases; not-pre/nonzero-link/free-type/count-at-least-two refutations, stability and phase preservation |
| `1746–1779` | `ireg_frzc`, Timeless, intro and off access/reintroduction |
| `1955–2085` | `ireg_rcol`, Timeless, intro/stability, claim and freeze agreement, flavored mint/spend, and native fragment-derived mint side conditions |

Unsigned source bitvector fields are represented by their exact natural values;
the source comparisons with zero are unchanged. The arbitrary `Dinode` carrier
is retained, including arbitrary address lists, major and minor fields. Only
`fresh_shape` requires the exact list of 13 zero addresses. Claim transaction
and positive share indices remain in the raw ledger claim. Raw absent and
invalid claim/freeze values are preserved, with the source's different truth
conditions: no claim is allowed, but an absent freeze column is rejected.

The reference predicate is exactly `r + rc ≤ n`, free type implies both
counters zero, and a present claim implies the plain counter is zero. The
licensed counter remains separate. The freeze predicate pins pre to count one
and post to zero, with nlink zero and nonzero type in both cases. Off imposes
no record or count condition. The phase theorem preserves the source's
explicit prohibition on moving off to a frozen phase without a separate mint.

`ireg_rcol` existentially retains the licensed counter beside actual native
ledger authority. `ireg_frzc` existentially retains the mirror bit beside its
actual half share. Neither predicate assumes the corresponding fact without
the native resource. Read-through laws derive typed claim/freeze agreement
and mint premises from authority and held fragments. The source mint/spend
laws use actual ledger updates and preserve all unchanged columns and names.

## Additional native composition

`count_mint` and `count_spend` combine these source column rules with the
existing native count camera. They require both supplied count halves and
first derive agreement of their values. They update both halves and the
reference ledger, returning the new halves with the exact minted unit or
consuming the supplied unit. They do not update a physical count or establish
an icache slot invariant. Their record/count/flavor hypotheses remain explicit.

`boot_rows` reorganizes already supplied ledger, count and mirror boot rows
for any finite set of signed inode keys and any inode-record function. It
retains both count halves, the freeze-off fragment, and both mirror halves
(one packaged into `ireg_frzc`). Reference counters are both zero, so no
record allocation/type restriction is required. This theorem does not mint
names or replace an existing authority, and leaves the separate window-pin
bundle available to frame.

The concrete `nativeSpec` uses the existing ledger slot 31 and coupling
capacities at slots 28–30. The mirror-only and count rules require no window
pin ownership. There is no new world, invariant allocation, or dependency on
`FsDurSnapshot.Initial`.

## Validation and remaining obligations

`python3 tools/lake.py build MachCSL.Logic.IcacheSlotCouplingLink` passed all
465 jobs. There are 46 named theorem declarations, plus the native Timeless
instances and generated definitions. The physical-origin audit is
`/tmp/xv6-lean-research/IcacheSlotCouplingOwnerAudit.lean`; it checks every
logical declaration, traverses types, opaque bodies and datatype constructors,
and rejects nonstandard axioms, unsafe/partial dependencies and initial
snapshot allocation. The audit passes all 102 logical declarations with only
`propext`, `Classical.choice`, and `Quot.sound`; zero roots are excluded, and
no unsafe/partial or initial-allocation dependency is present.

This is not the complete `ireg_slot`, full `icacheG`, or the inode-region
invariant. Claim transaction pins, freeze shelters, epoch receipts,
registry/ticket/corpse resources, top/record checked-out arms, and their
log-transaction coupling remain separate source dependencies. No such facts
are inferred from these pure predicates or from the cameras alone. The full
slot, its opening protocol, and runtime physical counter synchronization are
not claimed here.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
