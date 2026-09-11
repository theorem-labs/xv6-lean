# Independent review: spinlock worker and power-off frames

Reviewer: OpenAI Codex subagent `lean_logic_audit`, independently reviewing
coordinator-authored `SpinlockPoolWorkerFrames`, `SpinlockPoolPowerOffProofs`
and `SpinlockPoolWorkerCoverProofs`, with a subsequent independent review of
`SpinlockPoolBootProofs` and `SpinlockPoolPowerOnProofs`.
Verdict: **PASS for the stated frame and worker coverage scope**. The frame
modules rebuilt together (502 Lake jobs); the coverage module's compiled
theorems and boot/power-on modules were included in the fresh audit of all 49 originating declarations and full
logical cones, explicitly including opaque theorem bodies and inductive
constructors, found only the standard three axioms and no unsafe/partial
dependency or compiler-companion exclusion.

The UART proof covers every actual primitive and retains its actual observations;
all UART device updates preserve the reset Virtio component. Both PLIC arms
retain all cursor fields and use the proved 178-cell agreement that excludes
exactly the two physical pins. The disk proof consumes the actual language
step and reset invariant: every non-idle actor guard, including wild DMA, is
ruled out by `JalDevices.disk_step_idle`, and empty writes imply unchanged log
and memory. No reservation or device-preservation callback is assumed.

Power-off retains every occurrence, increments generation, and therefore makes
every old tagged generation strictly smaller than the new one. `Holds` is
false because the new state is off; a pre-crash unlock is unnecessary. The
durable disk is unchanged. The actual-step inversion is restricted by the real
`[powerOff]` observation, preventing it from covering a power-on transition.

Checked against pinned `RiscvLang.v` UART/PLIC actor definitions, the actual Lean
`Machine.Step` worker arms and `PowerStep`, and the reset-disk elimination proof.
Source pin: xv6iris arxiv-v1 `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
The coverage wrappers use the exact per-occurrence `AnnotatedPool.Covers`
conclusion, preserve left/right list contexts, and return the actual empty fork
list for UART/PLIC/disk/stale-hart/power-off cases. Stale harts are justified by
actual-step inversion and dead/live contradiction. Full coverage, power-on
initialization, live-hart framing and the final operational exclusion theorem
remain separate obligations.

Boot/power-on addendum: **PASS**. `boot_cursor` uses the universal actual
`BootFacts` theorem, retaining arbitrary pre-boot register files. Initial lock
and counter latest words follow from the loaded image and empty log.
`fresh_hart_iff` and `fresh_current` identify precisely the eight newly appended
CPU occurrences; old occurrences remain strictly stale, while all eleven actual
forks receive the correct labels. Power-on uses the actual `BootShape`, including
the generation equation and durable-disk retention, and establishes the entire
new `PoolInv`. No second boot precondition or chosen reset witness is assumed.
The full cover still needs the live-hart cases and final dispatch.

Evidence: `/tmp/xv6-lean-research/SpinlockPoolWorkerPeerAudit.lean` and
`/tmp/xv6-lean-research/spinlock-pool-worker-peer-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
