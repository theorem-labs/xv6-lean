# Independent log epoch and append-registry review

Reviewer: the Codex artifact-audit subagent, independently reviewing the
coordinator-authored `MachCSL/Logic/LogEpoch{Defs,Spec,Proofs,Link}.lean` and
`LogEpochSTATUS.md`. No production files were changed by the reviewer.
Result: **pass for the declared component scope**, with no correction requested.

The complete relevant source was checked at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`: `LogDefs.v:438–550` (names and
client fragments), `LogDefs.v:580–605` (full free-token allocation), and
`LogInv.v:1892–1926` (epoch bump and isolated allocations). Native
`Iris/BI/Lib/MonoNat`, `Iris/Algebra/LeibnizSet`, finite-set instances, Auth
updates and the preceding LogTx registry were also inspected.

| Source meaning | Checked implementation |
| --- | --- |
| `log_epoch_lb`, get/le/zero | Actual named MonoNat lower bound, preserved full authority on get, authority-backed numeric inequality, and native unit basic update at zero |
| `logged_at` | Actual Auth singleton fragment over the finite set of `(Nat, Int)` epoch/block pairs; both indices are retained |
| `log_mint_logged`, `logged_at_in` | Same-authority union update and remintable persistent singleton; membership follows from authority/fragment validity |
| `log_epoch_bump` | `epoch_update` generalizes the source successor increment to any explicitly monotone increase and returns the new receipt |
| `log_epoch_alloc`, `log_reg_alloc` | `allocate_genesis` constructs fresh named epoch authority at one and empty append authority while retaining an arbitrary frame |

The append camera uses the ordinary union `LeibnizSet` algebra. Its operation
is union and its core is itself, giving the required persistent, duplicable,
idempotent fragments. It is not the disjoint-set camera. The carrier is an
extensional finite tree set with lawful lexicographic order on arbitrary Nat
and signed Int keys. Its native lawful-set laws supply exact membership and
subset meaning, without restricting blocks to valid disk addresses or epochs
to current ones. Existing pairs can be reminted without an authority change;
adding a pair only grows the same set, preserving previously issued fragments.

The zero receipt is the raw MonoNat lower-bound ownership obtained by the unit
update. It is not a source-zero disjunction or an assertion that the current
epoch is zero. `epoch_update` explicitly requires `old ≤ next`; it does not
clear the append set, revoke old receipts or establish a journal transition.
The generic Spec's five fields are supplied by their actual native proofs.
Additional monotonicity, reminting, update and allocation theorems are proved
separately; there is no assumed backend implementation.

Allocation retains an arbitrary frame, so it can be used without consuming
existing resources. Both runtime names come from native allocators. The local
`capacity.monoNat 0` instance supplies the existing camera witness to allocation;
inspection of native `MonoNat.own_alloc`/`auth_own` confirms that the returned
fresh name, not that instance's placeholder name, indexes the ownership.
Epoch and append names live in different cameras and need not be numerically
distinct. This allocates only two components of the five-part source
`log_free_tok`; no lock, operation ledger, transaction ledger or whole log
invariant is asserted by the theorem.

The registry changes only slot 34, following LogTx slot 33. `registry_old`
preserves every slot below 34, and `registry_unused` preserves all slots at or
above 35. Epoch uses an explicit ElemG witness at the existing MonoNat slot 3;
there is no second counter camera. The explicit machine, invariant, UART,
filesystem, cache and transaction capacities retain their earlier slots and
native specification links. Sharing slot 3 does not identify epoch runtime
names with log-length, generation, start or inode-observation names.

Independent validation:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.LogEpochLink`
  passed 472 jobs (`/tmp/xv6-lean-research/log-epoch-peer-build.log`).
- `/tmp/xv6-lean-research/LogEpochPeerAudit.lean` audited all **156** logical
  declarations originating in the four modules, including generated/private
  declarations. It collected axioms and traversed types, opaque bodies with
  `value? (allowOpaque := true)`, and inductive constructors. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur; zero exclusions and no
  unsafe/partial semantic dependencies. Output: `log-epoch-peer-audit.log`.
- Explicit queries for append mint, genesis allocation and concrete registry
  Spec also passed the same allowlist.

A persistent receipt only says that its particular pair remains in the
append registry. Linking it to a live operation/current header, operation
budgets, commit, inode observation epochs, crash consistency and the full
`LogRes`/log invariant remains outside this reviewed layer. The code and STATUS
make those limitations explicit.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
