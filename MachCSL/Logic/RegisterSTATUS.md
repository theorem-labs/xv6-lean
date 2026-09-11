# Actual generated-register ownership bridge

Implemented against pinned `iris/RiscvPtsto.v` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, using the actual generated
`Register`, `RegisterType` and `MachCSL.Machine.RegisterFile` types.

| Source | Lean |
| --- | --- |
| `reg_pointsto` (1031–1033), explicit-hart form (2282–2284) | `regPointsto capacity γ r dq v`, with explicit runtime ghost name |
| `reg_agree` (1899–1901) | `RegAgree` |
| `reg_interp_at` (1904–1905) | `regInterpAt` |
| `reg_update_at` (2291–2308), `reg_update` (2353–2368) | `reg_update` |
| `reg_valid` (2343–2350), `reg_valid_dq` (2393–2401) | `reg_valid`, `reg_valid_dq` |
| `reg_interp_set_same` (2375–2389) | `reg_interp_set_same` |
| discarded persistence and `reg_pointsto_persist` (2405–2412) | `regPointsto_persistent`, `regPointsto_persist` |

The map keys are the actual generated enum, with a lawful order derived from
its compiler-provided constructor index. `ofNat_ctorIdx` is kernel-checked for
every constructor; it yields `ctorIdx_injective`, which proves the comparison's
lawful equality. Transitivity comes from native Nat comparison. No generated
source is modified, no register is represented by an unchecked integer key,
and no numeric key can denote a mismatched dependent payload.

Map values are `Sigma RegisterType`. A cell for register `r` owns exactly
`⟨r, v⟩`; `value_inj` extracts typed equality from same-key Sigma equality.
`RegAgree` is the exact one-way source relation: each present map cell equals
the corresponding actual register-file value. It permits a partial map, as
the source does. `regInterpAt` contains a full native ghost-map authority and
this pure relation; reads never infer concrete machine values from a fragment
without that authority and state tie.

`regAgree_write` proves that inserting the correctly typed value tracks the
actual dependent `MachCSL.Sail.Registers.write`. `reg_update` uses the native
frame-preserving ghost-map update, requiring full cell ownership, and reconstructs
the updated bridge. `reg_update_frame` retains any Iris frame. A same-valued
write uses the actual register-file equality and needs no writable fragment.
Fractional splitting, halves, typed cell agreement, timelessness and discarded
persistent ownership are also checked.

Initialization is complete and not an empty-map witness. `registerCount` is
computed from the final generated constructor; `ctorIdx_lt_count` checks every
constructor and `allRegisters_complete` proves every register occurs in the
enumeration. The computed count is proved equal to 180.
`initialMap_lookup` proves a correctly typed cell at every actual register;
`initialMap_agree` ties that complete map to any supplied actual register file.
`reg_alloc` allocates its authority and every full map fragment.
`initialCells_acc` exposes any selected typed register with its reassembly wand.
No register is automatically persisted or assumed to be permanently read-only.

The registry extension adds exactly slot 6 for this ghost map. Slots 0–5 are
preserved, with explicit derived `historyCapacity`, `viewsCapacity` and
`ledgerCapacity`; slots 7 and above remain unchanged. Runtime ghost names are
separate from slot capacity. Per-hart clients instantiate the explicit name
with their hart-to-name function; the global per-hart separation/accessor and
whole machine interpretation remain outside this slice.

`RegisterSpec.lean` imports definitions only. `registerSpec` proves that public
contract; `RegisterLink.lean` explicitly supplies all four proved contracts in
the seven-slot registry. The definitions/proofs do not import caller proofs or
assume an instruction WP.

Validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.RegisterLink
```

The build passes 329 jobs (proof module approximately 2.8 seconds, link 0.8
seconds). `/tmp/xv6-lean-research/RegisterAudit.lean` audits the entire new
namespace transitively, permitting only `propext`, `Classical.choice` and
`Quot.sound`; output is in `/tmp/xv6-lean-research/register-axioms.log`.
No custom axiom, `sorry`, native evaluator or bit-vector decision procedure is
used. The proof build does not depend on the active image certificate shards.

Outstanding: global per-hart interpretation and accessors, concrete allocation
and distribution during power-on, instruction WP lifting, full state
interpretation, backend correspondence and adequacy. This is a real register
resource bridge, not a kernel safety theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
