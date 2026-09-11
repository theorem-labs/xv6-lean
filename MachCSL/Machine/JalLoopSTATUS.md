# Repeated generated JAL execution

The 14 `JalLoop*.lean` modules prove finite local execution of the actual generated
`try_step 0 false` and `tick_clock ()` for every machine CPU (`Fin 8`). This is a
reusable execution foundation for the closed JAL gate. It does not prove that gate's
Iris weakest precondition, arbitrary global interleavings, or whole-system adequacy.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*

## Exact family and source

`registers cpu d` is the register file returned by the actual generated boot for
that CPU, overriding exactly `minstret`, `minstret_increment`, `mcycle`, `mtime`,
`mtimecmp`, `mip`, `sig_seip`, and `sig_meip`. All eight fields are unrestricted.
`boot_canonical` includes the real boot result; `plic_preserves` proves closure
under both actual PLIC pin-write arms, for every CPU.

The paper artifact is pinned at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; Sail RISC-V is pinned at
`23dcf8fd923eb8a1958795393d2975632aa940b2`. The Lean code uses the checked-in
`LeanPaperStock` generated model, with the corrected free runtime at
`28c729b5bb574ae7c32c13353403e57c575d85dd`. Principal source correspondences:

| Generated source | Checked result |
| --- | --- |
| `Step.lean:321`, `run_hart_active` | Exact dispatch, fetch, decode, next-PC writes, and JAL retirement; complete resulting RF equality. |
| `Step.lean:406`, `try_step` | `try_step_registers`: returns `false`, increments `minstret` modulo 2^64, and sets `minstret_increment` to true. |
| `Fetch.lean:232`, `fetch` | `fetch_registers`: actual fetched `F_Base 0x6f`, unchanged RF, all eight CPUs. |
| `InstsEnd.lean:17470`, `execute_JAL` | `execute_JAL_exec`: actual `JAL x0,0` writes nextPC and returns `Retire_Success`. |
| `Platform.lean:542`, `tick_clock` | `tick_clock_registers`: modular `mcycle` and `mtime` increments and exact MTI recomputation. |
| `Platform.lean:378`, `clint_dispatch` | Both changed-mip callback cases; disabled STCE preserves STI. Callback reads are retained. |
| `SysControl.lean:593`, `dispatchInterrupt` | No interrupt under the actual boot's Machine-mode global disable, for arbitrary pending bits and pins. |
| `Machine.Node.cycle` / `restart_step` | Both optional clock choices; actual pure-node restart clears reservations before the next cycle. |

The fetch certificate supplies precisely the eight observed static registers:
PC, misa, mstatus, cur_privilege, pma_regions, pmpcfg_n, pmpaddr_n, and
htif_tohost_base. Large PMP/PMA/HTIF values are the exact values from that hart's
boot result. No all-zero PMP assumption or changed finite representation is used.
Eight separate kernel reflection certificates cover all concrete hart IDs; a
small `Fin 8` proof combines them and transports to every symbolic `Dynamic`.

## Public entry points

Import `MachCSL.Machine.JalLoopWitness`.

- `try_step_registers` and `cycle_registers` characterize complete actual RF
  results, including wraparound, for arbitrary dynamic fields and both ticks.
- `cycle_nodeSteps` embeds every event in the existing concurrent node relation.
  It requires the stated canonical RF, valid reader view, and equality of the
  current TSO observation with the loaded JAL image.
- `repeat_nodeSteps` permits every finite Boolean clock-choice list, using actual
  restart steps and exact reservation clearing. It introduces no stutter rule.
- `boot_repeat_nodeSteps` discharges the RF and memory/view premises for each
  hart's actual generated boot result, empty log, and loaded JAL image.

Intermediate `*_fromFetch` lemmas deliberately expose the compositional fetch
premise. The Witness module discharges it; callers of the public results do not
supply a fetch theorem. `RegisterExec` and `FetchExec` retain event requests,
results, and state transitions in `Sail.Execution.Steps`. Their proof evaluators
are certificates, not replacements for machine semantics.

## Validation and proof engineering

`python3 tools/lake.py build MachCSL.Machine.JalLoopWitness` passes 169 jobs.
The all-eight-hart fetch module builds in 7.7 seconds (8.49 seconds measured wall
clock, 1,906,316 KB peak including the build invocation). No dependency or generated
model was changed for these proofs.

An origin-based audit checks all 794 logical declarations across the 14 modules,
including private helpers: only `propext`, `Classical.choice`, and `Quot.sound`
occur. The combined logical dependency cone contains no unsafe or partial
declaration. Two compiler-generated total-recursion runtime companions are
excluded as logical roots, following the repository audit policy; neither occurs
in a logical dependency cone. No native decision tactic or custom axiom is used.

Direct whole-state symbolic reflection was expensive. Abstract RF update laws
avoid repeatedly unfolding reset for each register constructor. Clock execution
uses compositional bind proofs, including all callback reads. Direct symbolic
PMP projection/fetch attempts exceeded bounded heartbeat or time limits; this
is a performance observation, not an impossibility claim. A single declaration
combining eight reflection proofs exceeded its checking budget; eight separately
checked certificates plus a small finite case proof build quickly.

## Remaining gate obligations

These results construct finite local runs. They do not establish all-successor
native Iris WP rules or closure under arbitrary UART, PLIC, DMA, and power
interleavings. In particular, the fixed-state register trace cannot by itself
justify asynchronous pin reads: an eventual WP proof must allow independently
changing pin values, use per-event ownership, and justify memory results at every
permitted TSO read view. Generation changes and dead-thread behavior remain part
of that global proof. A whole-model Rocq/Lean correspondence proof is separate.

The explicitly requested focused Fable 5.1 max review completed through Claude
Code. It found no semantic defect in the inspected canonical-family definitions
and local execution statements, while preserving the global and arbitrary-boot
limits above. Invocation details and disposition are in
[the focused review](../../docs/reviews/fable-jal-loop.md).
