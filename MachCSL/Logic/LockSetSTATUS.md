# Kernel held-lock sets and rank policy



Implemented the complete finite-name carrier and exact rank table/default
from pinned `LockRank.v`, and the native authoritative disjoint-set ownership
from `LockSet.v` (`RiscvPtsto.v:147`). This is a kernel resource prerequisite,
not an `acquire`, `release`, `holding`, or interrupt-handler WP.

The six modules are `LockRankDefs`, `LockRankProofs`, `LockSetDefs`,
`LockSetSpec`, `LockSetProofs`, and `LockSetLink`. They compile together in
405 Lake jobs; the two main proof modules took about 0.5 and 1.3 seconds.

| Source | Lean |
|---|---|
| `lock_ranks`, `rank_lookup`, `lock_rank` | `LockRank.ranks`, `lookup`, `rank` |
| `locks_below`, its decision instance | `LockRank.Below`, `belowDecidable` |
| `lock_rank_proc`, `lock_rank_kmem` | `rank_proc`, `rank_kmem` |
| table default | `lookup_absent`, `rank_default` |
| `locks_below_empty/not_elem/union_singleton/mono/difference/singleton` | `below_empty/not_mem/add/mono/difference/singleton` |
| `locks_add_del`, ranked variant | `add_delete`, `add_delete_below` |
| `size_add/del/del_lt/le_zero_empty/empty_le/add_le/del_le` | `size_add/delete/delete_lt/le_zero_empty/empty_le/add_le/delete_le` |
| `locks_self_del/union_empty/empty_del` | `self_delete/union_empty/empty_delete` |
| `lockSetR` | `LockSet.SetRA = Auth (DisjointLeibnizSet Names)` |
| `lk_auth`, `lk_in` | `LockSet.auth`, `member` |
| canonical `cpu_locks_at`, `cpu_locks` | `cpuLocks era cpu held` using `era.heldLocks cpu` |
| canonical fragment | `cpuMember era cpu name` |
| `lk_in_agree`, `cpu_locks_in` | `agree`, `cpu_agree` |
| `cpu_locks_not_in`, ranked variant | `not_member`, `not_member_below` |
| `lk_in_excl` | `exclusive` |
| `cpu_locks_insert`, ranked variant | `insert`, `insert_below`, `cpu_insert` |
| `cpu_locks_delete` | `delete`, `cpu_delete` |
| `cpu_locks_lvl_at`, ambient form | `level`, `cpuLevel` |
| level introduction/elimination | `level_intro`, `level_unfold` |
| level weaken/relevel/zero | `level_weaken`, `level_relevel`, `level_zero` |
| combined acquire/release depth steps | `level_insert`, `level_delete` |
| empty-set initialization ingredient | `allocate` returns a fresh authority |
| proof contract and implementation | `LockSetSpec`, `actual`, `registrySpec` |

All sets are actual finite `Std.ExtTreeSet String` values; there is no
restriction to names in the rank table. Singleton fragments are exclusive,
and deletion consumes the fragment. Insertion requires exactly the source
freshness premise. The source rank-based policy is available separately;
none of these laws asserts termination or fairness of acquisition.

Registry slot **26** extends `FsTop.registry` without changing slots 0–25.
The existing lock state/position product is still at 24, inode map at 25,
and all machine, heap, TSO, observation, UART, and invariant capacities have
explicit lifts. No existing registry definition is edited. The era wrappers
reuse `Era.Record.heldLocks`; data in those fields is not evidence of resource
allocation. Connecting fresh sets to all eight CPU boot resources remains
unproved and is not added as an assumption to any existing boot theorem.

The broader dependency analysis is in
[`kernel-spinlock-port.md`](../../../docs/design/kernel-spinlock-port.md).
The kernel's owner-field window, word pin, context floors and parked payload,
Supervisor capability, translated instruction fetch, and interrupt crossing
remain separate work. This module does not replace them with the two-hart
test's simpler protocol. Source-to-Lean cross-prover correspondence also
remains a separate obligation.

Validation: `python3 tools/lake.py build MachCSL.Logic.LockSetLink` completed
405 jobs successfully. A fresh physical-module audit checked all 193 logical
declarations in the six modules, traversing opaque theorem bodies and
constructors. Their dependency cones use only `propext`, `Classical.choice`,
and `Quot.sound`, with no unsafe or partial implementation dependencies.
The audit excluded one compiler-generated runtime companion for the total
rank lookup from its declaration roots; the logical lookup itself and its
full dependency cone were checked. Raw audit evidence is retained outside
the repository in `/tmp/xv6-lean-research/lock-set-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
