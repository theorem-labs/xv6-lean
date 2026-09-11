# Eight-hart register interpretation

Implemented against pinned `iris/RiscvPtsto.v` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:

| Source | Lean |
| --- | --- |
| `gregs_interp` (1976–1977), `gregs_interp_at` (2083–2086) | `gregsInterp` with explicit `CPU → GName` |
| `gregs_interp_acc` (2248–2264), `gregs_interp_acc_at` (2311–2330) | `gregs_acc` for any actual CPU |
| per-hart `reg_valid_dq` / `reg_update` | `gregs_read` / `gregs_write`, composed through the accessor |
| repeated per-hart register-map allocation | `gregs_alloc`, returning all names and all initialized cells |

`CPU` is the actual machine `Fin 8`. `allCPUs` is the native finite extensional
set constructed from `List.finRange 8`; `mem_allCPUs` proves membership for every
actual hart. The global interpretation is the source's finite separating
conjunction of authoritative per-hart bridges. No hart-membership premise is
left to a caller, and no shared name, era equivalence or global state
interpretation is assumed.

`gregs_acc` returns the selected bridge and a wand universally quantified over
its replacement register file. Reassembly produces exactly
`Machine.updateHart files cpu replacement`; every other CPU retains its former
bridge. `gregs_write` uses the actual dependent `Sail.Registers.write` inside
that exact update. `gregs_write_frame` additionally retains an arbitrary Iris
frame. Reads require both the global authority and the selected typed cell at
its supplied fraction.

Allocation is proved by finite-set induction. Each insertion invokes the
per-hart allocator, updates an explicit total name function at the fresh hart,
and preserves all existing harts' resources. Applying the proof to `allCPUs`
allocates all eight actual register files, returning both their interpretations
and the finite separating conjunction of their complete initial cell bundles.
Names are allocated by native Iris updates, not supplied as assumed constants.
No separate pairwise-name-injectivity claim is exported. `initial_reg_acc`
exposes any selected hart/register cell with a wand that restores the full
initialization bundle; it composes the finite-set accessor with the proven
per-hart complete-map accessor.

This slice adds no resource capacity or registry slot. The same explicit
`Registers.Capacity` is used throughout. `GlobalRegistersSpec.lean` imports
only definitions and the per-hart `RegisterSpec`. Its proof implementation
takes that per-hart contract as an explicit argument and never imports the
per-hart proof implementation. `GlobalRegistersLink.lean` supplies the checked
`Registers.registryRegisterSpec` and exports `registryGlobalRegisterSpec`.

Validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.GlobalRegistersLink
```

The 341-job build passes; the global proof module takes about 2.6 seconds and
the link module about 0.9 seconds. The whole namespace is audited transitively
by `/tmp/xv6-lean-research/GlobalRegistersAudit.lean`, with log
`/tmp/xv6-lean-research/global-registers-axioms.log`, allowing only `propext`,
`Classical.choice` and `Quot.sound`. No `sorry`, custom axiom, native evaluator
or bit-vector decision procedure is used. No image certificates are imported.

Outstanding: power-on allocation and distribution in the complete machine
state interpretation, era ownership, instruction WP rules and adequacy.
The result supplies the exact global register resource component, not the
full machine state interpretation or a kernel safety theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
