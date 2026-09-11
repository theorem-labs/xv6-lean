# Actual fetched-cycle event plans and native WP

The six `JalLoopPlan{,Eval,Instruction,Cycle,Fetch,Link}` modules and four `Logic/EventWPCode`, `EventWPJal{Spec,Proofs,Link}` modules are checked and frozen at this checkpoint. They replace the earlier existential trace premise with universally branching plans of the actual free-event tree and a native-Iris per-cycle WP.

The plan retains independently varying results at every hardware pin read. Its register table describes the 178 owned CPU cells; the table's two ignored pin entries do not assert actual physical pin values. All register and RAM events remain individual machine steps. The existing EventWP fold restores owned registers and concrete four-byte/pristine RAM resources through each event; no full-instruction atomicity is introduced.

The generated source paths are preserved:

| Actual model path | Checked plan |
| --- | --- |
| `InterruptRegs.read_mip`, platform CSR callback | `readOnly_plan`, `mip_callback_plan`; universal and independent pin results |
| `SysControl.getPendingSet`, `dispatchInterrupt` | `getPendingSet_plan`, `dispatchInterrupt_plan`; only reset mstatus is required, while interrupt masks, delegation, pending bits and pins may vary |
| `Platform.should_inc_mcycle`, `should_inc_minstret` | exact source guards, arbitrary inhibit/configuration registers and privilege |
| `Platform.clint_dispatch`, `tick_clock` | all modulo-counter cases, both increment branches, unsigned timer comparison and actual changed-mip callback reads; only menvcfg=0 is required |
| actual `ext_decode` and `execute_JAL 0 x0` | checked partial/register evaluators reject all pin accesses and unsupported events; scalar reset facts suffice |
| `Step.run_hart_active`, `try_step`, `Node.cycle` | `active_plan`, `try_step_plan`, `cycle_plan`; actual retirement guard, both retirement branches, all counter overflow, both clock choices |
| actual instruction `fetch` | `fetch_checked` and `fetch_plan`; an oracle accepts exactly four bytes at the JAL vector with word 0x6f, preserving the entire request and result in the event |

`registerPlanRun_plan` and `snapshotPlanRun_plan` prove soundness of total, fuel-bounded proof evaluators that reject unowned pin events. The fuel does not restrict machine executions. The snapshot evaluator uses an explicit partial RAM oracle; it does not assume the whole loaded RAM is owned. `EventWP.codeRamAccess` discharges its interface with the actual four byte cells and pristine timestamp predicates, extracting and restoring both. There is no assumed callee WP in that resource contract.

`EventWPJal.registryJalCycleWPSpec` links the actual event, register and RAM implementations at the common 23-slot UART/PLIC registry. The WP holds for both clock choices, with arbitrary counter filter settings and all pin-result combinations, and returns its owned CPU cells and code resources to the actual pure-node WP continuation. That continuation remains an obligation; the pure node is the machine's restart node, not a native language value.

The remaining boot restriction is explicit. `Static` is the thirteen-field `BootUniversal.StaticBoot` predicate, which has been proved for every actual BootFacts prestate. `SnapshotCovered`, however, still fixes the PMP configuration/address slice to each hart's previously checked concrete reset witness. No theorem here infers this stronger snapshot premise from arbitrary BootFacts. Universal OFF-only PMP fetch, the guarded per-hart loop, all-eight-hart initial resource allocation, other actors, power-handler composition and closed adequacy remain separate work. The cycle transformations preserve `Static` and the current explicit snapshot predicate.

Validation: concrete native link passed a 465-job dependency build. The complete fresh physical-module-origin audit covered 179 logical declarations in ten modules, including private helpers, with only `propext`, `Classical.choice`, and `Quot.sound`. Two compiler-created total-recursion runtime companions were excluded as audit roots; neither they nor any unsafe/partial declaration occur in the combined logical dependency cone. Both `fetched_cycle_plan` and `registryJalCycleWPSpec` use only the standard three axioms. Audit: `/tmp/xv6-lean-research/JalPlanAudit.lean`, log `jal-plan-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
