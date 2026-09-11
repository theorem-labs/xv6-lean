# Native supervisor write-address announcement

Implemented and frozen: SupervisorWriteEA{Defs,Spec,Plan,Proofs,Link}.
`program_plan` proves the actual eight-byte ordinary Data `mem_write_ea`
returns `Ok ()` with unchanged register file. `wp_announce` and the constructed
`nativeSpec` fold this concrete plan through actual native register WPs.

The footprint has five independently fractional cells: mstatus, current
privilege, PMA regions, PMP configuration array, and PMP address array. The
six actual reads are mstatus, current privilege, PMA, PMP configuration,
PMP configuration again, and PMP address. The generated singleton split loop,
zero-offset address arithmetic, pure assertions and Write_plain selection
remain in the proved program. No register is written. `announcement` proves
the actual `write_ram_ea` is pure unit; no HTIF/MMIO check or memory-write
event is part of this prefix.

`Config` exposes concrete actual conditions: Supervisor privilege, MPRV zero,
positive supervisor TOR/RAM grant, width-eight RAM interval, matched writable
PMA region and explicit eight-byte physical alignment. No other status or
configuration field is fixed. The gate needs no word assertion, selected
memory result, translation WP or other software/state oracle. It introduces
no ghost camera. Any reservation/context/memory resources may be framed;
this prefix does not clear reservations, advance a view, or append a log.
Those effects belong to the subsequent value-write stage. Separate real
register events remain interruptible, with native generation/dead-thread
handling inherited from the proved register fold.

The proof reuses `SupervisorBare.effective_supervisor`, native
`SupervisorWrite.priority_store_plan`, and `SupervisorPmp.check_ram_plan`.
The two effective-privilege reads are assembled directly inside the actual
ExceptT program because its generated lift grouping differs from the outer
value wrapper; neither read is removed or represented by an assumed effect.

Source correspondence at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`: the bounded eight-byte specialization
of `HartSMem.v:2845–2928` (`swp_mem_write_ea_S`). Its abstract PMA/access
premises are discharged through actual matched-region and RAM/PMP facts.
Generated definitions: `Mem.lean:497–530` and
`PhysMemInterface.lean:329–331`. Both source `HartSMem.v:3229–3245` and actual
`VmemUtils.lean:399–407` call this stage before the separate value write.
Later virtual-store composition must retain both stages.

Validation: `python3 tools/lake.py build MachCSL.Logic.SupervisorWriteEALink`
passed **467 jobs**; Plan 1.1 s, Proofs 1.0 s, Link 829 ms. Fresh physical-origin
audit checked all **65 declarations** in the five modules, including private
helpers, transitive types, opaque bodies and inductive constructors. Only
`propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe/partial logical
dependency and zero excluded compiler runtime companions. `announcement`
itself has no axioms. Evidence:
`/tmp/xv6-lean-research/SupervisorWriteEAAudit.lean`,
`supervisor-write-ea-audit.log`, `supervisor-write-ea-build.log`.
No sorry, custom axiom, native decision tactic or frozen-file edit.

This establishes the permission/announcement prefix only. It does not prove
a memory store, virtual address formation or transformation, Bare/KPT store
composition, an instruction WP or a complete kernel function. Whole generated
model to Rocq correspondence remains a separate documented project limit.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
