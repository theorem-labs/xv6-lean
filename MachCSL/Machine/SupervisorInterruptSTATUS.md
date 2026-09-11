# Disabled-SIE supervisor interrupt dispatch

`SupervisorInterrupt{Defs,Proofs,Plan}.lean` proves that the actual generated `getPendingSet Supervisor` and `dispatchInterrupt Supervisor` return `none` from the source's interrupt-disable conditions. `Disabled rs` requires only `misa.S = 1`, `mie & ~mideleg = 0`, and the exact Boolean SIE test equal to false. The remaining `misa` and `mstatus` bits, all `mip` bits and both external pins are unrestricted. `sie_zero` checks the equivalent one-bit-zero formulation. No full reset-register constant is required.

`currentlyEnabled_s_plan` pays the actual `misa` read and proves Ext_S enabled from its S bit and the stock model's checked S/Zicsr support. `external_plan` and `read_mip_plan` cover independent universal result branches for `sig_meip` and `sig_seip`. Their postconditions expose exactly the generated MEI/SEI update construction and the OR with the existing `mip`, with the symbolic register file unchanged. The existential pin values in those result formulas describe the results of universal `ExecPlan.readPin` branches; they are not caller-selected values or assumptions that pin reads equal `rs`'s pin fields.

The actual read sequence of `getPendingSet_plan` and `dispatch_plan` is:

1. `misa` for the initial Ext_S check;
2. `mideleg`;
3. `mip`;
4. `sig_meip`, with every one-bit result covered;
5. `misa` for the external-interrupt Ext_S check;
6. `sig_seip`, independently covering every one-bit result;
7. `mie` for machine-destined pending bits;
8. `mie` again for supervisor-destined pending bits;
9. `mstatus` for MIE;
10. `mstatus` again for SIE.

In particular, the generated eager Lean `do` expression reads MIE's `mstatus` even though the explicit privilege is Supervisor and the Machine comparison is false. The source Rocq proof uses short-circuit monadic Boolean helpers; this plan follows the actual generated Lean events instead of dropping that read. There are no register writes or memory events. The unchanged file is the `EventWP` symbolic register table; the theorem does not forbid asynchronous physical pin changes by another worker between reads.

`machine_pending_zero` derives zero machine-destined pending bits for any pending word from the delegation mask. The Supervisor case makes the machine global-enable expression true, but its pending set is zero. The supervisor pending set remains arbitrary and is ignored because SIE is false. `dispatch_plan` composes the resulting `none` directly, without selecting a priority interrupt or entering a trap handler.

Source mapping at pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:

- `iris/SmodeCore.v:65–154`: `and_vec_zeros64_r`, `exec_read_mip_some_S`, `exec_getPendingSet_supervisor_none`, and `exec_dispatchInterrupt_none_S` map to `machine_pending_zero`, `read_mip_plan`, `getPendingSet_plan` and `dispatch_plan`. The source Ext_S execution premise is discharged here from the exact S bit and fixed model support, without a callee execution oracle.
- Generated `LeanPaperStock/PlatformConfig.lean:2556–2582`: `currentlyEnabled` and its Zicsr dependency.
- `LeanPaperStock/InterruptRegs.lean:662–678`: exact external pin composition and `read_mip IncludePlatformInterrupts`.
- `LeanPaperStock/SysControl.lean:570–600`: pending-set and dispatch definitions, including both eager status reads.

Validation: `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Machine.SupervisorInterruptPlan` passes all 391 jobs; the plan module checks in 997 ms. The fresh physical-origin audit checks every one of the 20 declarations in the three modules, with zero exclusions and complete opaque-body/type/constructor dependency traversal (`info.value? (allowOpaque := true)`). Only `propext`, `Classical.choice` and `Quot.sound` occur. No new axiom, `sorry`, native decision procedure, unsafe or partial semantic dependency occurs. Evidence: `/tmp/xv6-lean-research/SupervisorInterruptAudit.lean`, `supervisor-interrupt-audit.log` and `supervisor-interrupt-build.log`.

This is a read-only `EventWP` proof-plan boundary for an explicit Supervisor argument. It does not establish the surrounding current-privilege ownership, partial-register resource package, interrupt-handler invariant, clock stability, supervisor translation or a complete kernel instruction WP. Native ownership packaging remains separate. No registry slot, generated semantics or previous PMP module was changed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
