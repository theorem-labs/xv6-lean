# Native inode-reference claim and freeze ledger

Status: owner build, full dependency audit and independent coordinator source review passed.
Source: xv6iris `arxiv-v1`, `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The exact source camera is a finite map from signed inode keys to **per-key**
authoritative elements:

```
ExtTreeMap Int (Auth (((ClaimCell × NatAdd) × FreezeCell) × NatAdd))
```

This is the inode cache's `linkUR`, distinct from filesystem `fsLinkUR` at slot
23. It is not an authority over the whole finite map. `NatAdd` is a concrete
wrapper of Nat carrying addition, zero core and unconditional validity; its
operation and inclusion-to-≤ correspondence are proved. This avoids altering
instances for unrelated counters. Public counter arguments remain Nat.

`ClaimCell` and `FreezeCell` retain the full `Option (Excl (DiscreteO _))`
carriers, including absent and invalid exclusive values. Claim values are
`BitVec 16 × (Nat × Qp)`. Freeze phases are `off`, `pre index`, `post index`,
with `index : Bool × (Nat × Qp)`. No type, transaction, share, phase or regime
field is erased or existentially weakened.

| Pinned source | Lean counterpart |
| --- | --- |
| Xv6Cameras.v 615–712 | Typed claim/freeze carriers, exact three nested products, per-key Auth finite-map camera and generic `Capacity GF` |
| IcacheRef.v 333–441 | `frz_ispre`, `frz_preb`, `frz_reg`, `lelem0`, `lelemc`, `lelemf`, `lelem` |
| IcacheRef.v 1300–1430 | `link_auth_e`, `link_frag_e`, `link_auth`, typed `iclaim`, both reference flavors, `rup`/`rcup`, freeze tokens; Timeless instances |
| IcacheRef.v 1435–1565 | Raw inclusion and validity; both counter bounds; claim and freeze agreement; freeze exclusivity (also direct claim exclusivity) |
| IcacheRef.v 1575–1748 | Actual product/option/additive local updates, source authority/fragment update lifting, claim mint/spend, separate counter mint/spend and flavor wrappers, held-token freeze rephasing |
| IcacheRef.v 543–600, 1990–2011 | Exact `● lelem_boot • ◯ lelem_boot` finite boot map, validity/lookup, supplied-map split, native allocation preserving the frame |

`runit_any` is **plain only**, exactly as the pinned source's C' conversion
discipline requires. It is not an existentially forgotten flavor. The two
reference counters remain separate throughout every update.

`link_mint_claim` requires an absent claim cell. Spending takes the matching
typed claim fragment. `link_freeze_step` takes the existing freeze fragment and
returns the rephased one with the authority; it cannot be applied to an
authority alone. Pure validity and inclusion proofs supply the corresponding
agreement facts without assuming a complete inode slot or transaction resource.

`link_boot_split` accepts already supplied map ownership over an arbitrary
finite set of signed inode keys, including the empty set. Every row yields the
empty-claim/two-zero-counter authority with `FrzOff` and its separate full freeze
fragment. `allocate` proves the fresh-name version in the same supplied native
world while retaining the original arbitrary frame. No invariant world is
allocated and no existing authority is replaced.

The registry extends `IcacheCoupling.registry` at assigned slot 31 and proves
slots 0–30 and 32 onward unchanged. Explicit capacities retain the three
coupling cameras, record camera, held-set, lock, filesystem top/link, UART,
invariant and full existing machine resources.

Validation: seven modules, 65 named laws, 460-job Link build passed. The owner
physical-origin audit checks all declarations and recursively traverses types,
opaque bodies and inductive constructors. Standard `propext`, `Classical.choice`
and `Quot.sound` are the only allowed axioms; unsafe/partial logical dependencies
and `FsDurSnapshot.Initial` constructors are rejected. All 308 physical-origin
logical declarations passed, with zero excluded roots.
Audit source: `/tmp/xv6-lean-research/IcacheRefLedgerOwnerAudit.lean`.

Remaining source layers: the complete `ireg_ref_ok`/claim/freeze/mirror and record
coupling; type one-shot boot shelter; log transaction pins and observation
receipts; actual escrow registry/tickets/corpses and pending payload; full inode
slots, region invariant and complete icache bootstrap. Algebra alone does not
establish those missing resource facts or license their replacement by an oracle.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
