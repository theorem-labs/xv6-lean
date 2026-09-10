# Independent device fabric and global-state review

Reviewed `MachCSL/Devices/{Fabric,FabricProofs}.lean` and
`MachCSL/Machine/{State,DeviceSteps}.lean` against `DevModel.v:950–1140` and
`RiscvLang.v` in paper tag `arxiv-v1`, commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
No mismatch was found in the inspected source transcription. This review covers
the fabric and actor composition; the UART/PLIC/Virtio component proofs and
remaining source-carrier correspondence are separate prerequisites.

## Fabric

The decode order and exact widths match
[`DevModel.v:dev_read/dev_write`](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/DevModel.v#L1002-L1082).
UART widths 1, 2, 4 and 8 address one byte register, with zero extension on read
and low-byte truncation on write. PLIC accepts only width 4. Virtio accepts width
4 through its register decoder; widths 1 and 2 return zero or discard a write
anywhere within its window, even if that offset is not a decoded 32-bit register.
Other widths and unmatched device addresses remain stuck. No new alignment or
whole-access-window check was inserted into the source fabric.

Only UART/PLIC reads can update their component. `read_disk` and `write_disk`
match the source durable-disk framing lemmas; the latter explicitly depends on
`Virtio.virtio_write_disk`, including its reset case. IRQ source selection and
M/S context wiring match `dev_irq_level`, `dev_meip` and `dev_seip`. Fabric reset
uses initial UART/PLIC state and the Virtio reset that retains durable bytes.
These definitions supply the concrete `Machine.Bus` instance previously absent
from the hart-local rules. They do not yet supply the complete global language.

## Global state and actors

The fields of `State` match `gstate`, including generation, power, reservations,
era image, write log and per-hart views. `MemoryOK` retains all three conjuncts
of `mm_ok`; `ReservationsOK` is the source snapshot/submap condition, without
inventing pairwise reservation disjointness. `othersReserved` and `allReserved`
are extensional versions of the source finite unions over eight CPUs. Their
representation bridge to the source set/map libraries remains to be proved.

`HartStep` focuses one hart, takes one concrete-bus node step, and writes back
exactly its register/reservation/view slots and shared memory/device/log fields.
It retains era image, generation and power. This matches the ungated
`hart_node_step` core. **`ThreadLive` is currently a definition, not a premise of
`HartStep`:** the source applies live/dead generation gating in `prim_step`.
The eventual global relation must add that gating and the corresponding dead
thread rule, rather than treating this core as the entire global semantics.
`hart_flat` proves only its stated memory/log invariant, not complete preservation
of `MemoryOK` and `ReservationsOK`.

Every constructor of
[`uart_step`](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/RiscvLang.v#L489-L503)
is retained: normal/loopback transmit, accepted receive, UART-source latch and
explicit idle. Loopback transmission emits no output observation. Rejected
receive attempts emit none because they do not constitute a receive step.
`uart_wire` correctly identifies output observations with growth of the UART
wire trace, and `uart_disk` preserves durable disk bytes.

Both
[`plic_step`](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/RiscvLang.v#L616-L625)
constructors remain: an independently scheduled update of one hart's S or M
interrupt pin. No synchronous pin update is added to MMIO and no pin value is
assumed fixed. The relation needs no extra idle constructor because either
source constructor can always select a hart.

The disk/DMA actor, crash/reboot generation transitions, fork set, and complete
Iris language/adequacy are outside these files. The resulting partial collection
of actors must not be reported as a closed whole-machine proof.

## Validation

Source inspection and compiled checks are complete for these files. Independent
imports and axiom checks of `read_disk`, `write_disk`, `hart_flat`, `uart_wire`
and `uart_disk` succeed on Lean 4.32.2. Their dependency cones contain only
`propext`, `Classical.choice` and `Quot.sound`. This checks these selected results,
not every declaration in the imported Virtio namespace; the root package audit
must independently reject generated custom axioms in unused declarations too.
Kernel-checkable ordinary proof terms, not native decision certificates, are the
acceptance criterion.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
