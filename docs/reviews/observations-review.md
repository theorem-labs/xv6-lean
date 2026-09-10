# Independent observable-history review

PASS: the reviewed definitions and theorems preserve the complete pure
`iris/ObsTrace.v` vocabulary and its scheduling scope at paper commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The entire 448-line source was read,
along with the relevant UART/fabric, node, disk, power and thread-pool definitions.
No production source changes were required.

Reviewed hashes:

- `MachCSL/Machine/DevicePreservation.lean`:
  `0c1b9cc1b5f303adf25a8936248aae86f52a08179d9d78a0b306dd10e2e5e9d1`.
- `MachCSL/Machine/Observations.lean`:
  `49803c454c8bf53116138b275b74f9ac2fc67b3196416b3056c8360644551826`.
- `MachCSL/Machine/ObservationCycles.lean`:
  `c1aa45c93f860c4e73f09719aecd15b3b2fc520d3637a831b84e6283edf36dae`.

| Pinned source symbols / lines | Lean correspondence |
| --- | --- |
| `obs_wire`, `obs_wire_app`, 47–59 | `DeviceSteps.outputBytes`, `outputBytes_append` |
| UART wire laws, 62–106 | `Devices.Uart` receive/pop/push/read/write field and trace laws |
| `dev_read_u_wire`, `dev_write_u_wire`, 110–129 | `Devices.FabricProofs.read_wire`, `write_wire` |
| `uart_step_wire`, `uart_step_io`, 137–162 | `DeviceSteps.uart_wire`, `uart_observations_io` |
| `mnode_step_u_wire`, `disk_step_duart`, 168–195 | Generic `node_device_projection`, `hart_wire`; `DiskSteps.disk_uart` |
| `is_io`, `obs_step`, `trace_shape`, 152,208–235 | `isIO`, `observationStep`, `TraceShape` and nil/snoc/IO laws |
| `obs_boots`, append/IO laws, 239–255 | `bootCount`, `bootCount_append`, `bootCount_io` |
| `seg_step`, `open_seg` and fold laws, 259–287 | `segmentStep`, `openSegment` and append/IO/power laws |
| `obs_wf`, initialization, 294–307 | `ObservationsOK`, `observations_init` |
| `prim_step_obs_wf`, 309–349 | `step_observations_ok` |
| `step_obs_wf`, `nsteps_obs_wf`, `run_obs_wf`, 359–383 | `poolStep_observations_ok`, `poolSteps_observations_ok`, `run_observations_ok` |
| `cyc_step`, `cycles_rev`, `cycles_of`, 396–404 | `cycleStep`, `cyclesReverse`, `cyclesOf` |
| Cycle append/head/on/off/IO laws, 406–448 | `cyclesReverse_append`, `traceShape_cycles`, `cyclesOf_on`, `cyclesOf_off`, `cyclesOf_io` |

Key checks:

- The history retains input, output, PowerOn and PowerOff in one interleaved
  list. Output-only projection is used solely for the physical-wire tie.
- The automaton starts off, permits IO only while on, and alternates legal on/off
  transitions. `none` remains an absorbing rejection state. The boot-count
  equation is exactly `generation + (if power then 1 else 0)`.
- The UART wire grows at the autonomous transmit step, not at a THR MMIO write.
  Loopback produces no external output event and no wire growth. Input events
  mark accepted input; no invented cumulative input-state equality is asserted.
- CPU register/RAM/restart events preserve device projections. MMIO cases rely
  on proved concrete bus preservation, rather than assuming the whole fabric is
  unchanged. Disk transitions, including wild writes, preserve the UART itself.
- PowerOff increments the generation and disables the wire obligation. PowerOn
  retains that generation, appends the next boot event and resets the UART wire.
  Both power events clear `openSegment`; only PowerOn adds a cycle to `cyclesOf`.
  A completed cycle is retained when power turns off. Malformed histories retain
  the source's total cycle-fold behavior; correspondence with the current open
  segment requires the explicit `TraceShape history true` premise.
- `PoolStep` and `PoolSteps` are aliases of the installed Iris library's actual
  thread-pool `Language.Step`/`NSteps`. Their atomic rule can select any thread
  with arbitrary left/right context and includes forked threads. The run theorem
  quantifies over every finite length, initial/final pool, state, history and
  derivation; its initial assumptions are only powered-off and generation zero.
  No selected schedule, fairness assumption, scheduler restriction, memory
  invariant or client-content invariant was added.

The theorem establishes trace shape, boot count and current-cycle UART wire
correspondence. It does not establish kernel safety, per-cycle console content,
filesystem properties, hart reducibility, progress, fairness or an infinite-run
liveness theorem. Those limitations match the source's distinction between its
pure observation invariant and the client adequacy/content proof. In particular
this is not the exported `xv6_obs_wf` system corollary by itself.

Validation: the current compiled `ObservationCycles` import passed an independent
enforced `Lean.collectAxioms` audit for all 24 handwritten proof roots across the
three reviewed files. Every transitive axiom was among `propext`,
`Classical.choice` and `Quot.sound`. No added or native-decision axiom occurs.
Scratch driver/log: `/tmp/xv6-lean-research/ObservationsAudit.lean` and
`observations-axiom-audit.log`. These temporary files are review artifacts, not
required repository build inputs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
