# Native icache count, freeze-mirror and window-pin coupling

Status: owner build, full dependency audit and independent coordinator source review passed.
Baseline: xv6iris `arxiv-v1`, `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

This slice implements three actual distinct source cameras:

| Source camera | Lean carrier and slot |
| --- | --- |
| Xv6Cameras.v `icntUR` | `ExtTreeMap Int (DFracAgree (DiscreteO Nat))`, slot 28 |
| Xv6Cameras.v `frzmUR` | `ExtTreeMap Int (DFracAgree (DiscreteO Bool))`, slot 29 |
| Xv6Cameras.v `hpnUR` | `ExtTreeMap Nat (DFracAgree (DiscreteO (Option (Nat × Qp))))`, slot 30 |

The source maps have no authoritative column. The full discardable-fraction
camera carrier is retained, while the source predicates expose positive owned
fractions. The pin's transaction identifier and share are fields of its value,
so agreement recovers the exact pair; it is not reduced to a Boolean.

`Defs` exports the three generic `Capacity GF` fields, three explicit names,
`icnt_at` / `icnt_half` / `icnt_full`, `frzm_at` / `frzm_h` / `frzm_full`, and
`hpn_at` / `hpn_h` / `hpn_full`. These are the exact IcacheRef.v 1761–1943
predicates. `Proofs` supplies Timeless instances, arbitrary-fraction splitting,
full-to-two-halves splitting, half agreement and both-halves/full updates.
The count/mirror/pin law prefixes identify the corresponding source families.

`BootProofs` matches IcacheRef.v 530–580, 907–939 and 1946–1990:

- Count and mirror maps range over an arbitrary finite set of **signed** inode
  keys, at zero and false respectively. Empty sets are included.
- The pin boot map is the source ordered product of singleton cells at
  `List.range 50`, all at `none`; 50 is the exact source `NINODE` at line 143.
- `icnt_boot_split`, `frzm_boot_split` and `hpn_boot_split` consume already
  supplied map ownership; none requires a fresh allocation.
- `hpn_boot_halves` checks the split of all 50 full pins into both source halves.
- `allocate` creates these three valid maps in the existing native world and
  returns both count/mirror halves, all 50 full pins and the original arbitrary
  frame. It does not allocate an invariant world or claim a full `icacheG`/`icfg`.

The registry extends `FsInodeRegion.registry` at slots 28–30 and proves all
slots 0–27 and 31 onward unchanged. Explicit earlier record, held-set, lock,
filesystem-top/link, UART, invariant and machine capacities remain available.

Validation: the combined Link build passes all 453 jobs. The five modules
contain 57 named public/private laws. The physical-origin audit traverses every
one of 231 logical declarations, its full type, opaque body and inductive constructors;
only the standard three foundational axioms are allowed, and native durable
initializers and unsafe/partial semantic dependencies are rejected. All 231
passed with zero excluded roots. Audit source:
`/tmp/xv6-lean-research/IcacheCouplingOwnerAudit.lean`.

Remaining dependencies: the distinct icache `linkUR` claim/plain/licensed-
reference/freeze ledger; freeze-phase carrier and `ireg_frzc` coupling;
type one-shot boot shelter; escrow registry/tickets/corpses and pending payload;
transaction pin resources, observation receipts, complete inode slots and region
invariant. This slice does not replace any of those resources by an oracle.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
