# UART port status

The pure UART device model and all 24 actual UART lemmas in
`iris/DevModel.v:94–729` at paper commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476` have Lean counterparts.
There are 49 public theorems, including 25 additional field, interrupt, FIFO and
regression laws. This is a pure device port; it is not a machine-level UART
safety theorem, a driver proof, or whole-system verification.

The complete source UART section was read before implementation. The board reset
at `DevModel.v:1129–1137` was read and ported as well. No changes were made to the
root umbrellas, device bus or machine transitions by this workstream.

## Definitions and representation

All names below are in `MachCSL.Devices.Uart`.

| Pinned source | Lean definition |
| --- | --- |
| `uart_state`, its thirteen `u_*` fields | `State`, same field order with `u_` removed |
| `uart_base`, `uart_size`, `uart_irq_id`, `uart_fifo_depth` | `base`, `size`, `irqId`, `fifoDepth` |
| `byte0` | Literal zero at `Byte := BitVec 8` |
| `uart_dlab`, `uart_fifo_en`, `uart_loopback` | `dlab`, `fifoEnabled`, `loopback` |
| `uart_rx_ready`, `uart_thre` | `rxReady`, `thre` |
| `uart_rx_int`, `uart_tx_int`, `uart_irq` | `rxInterrupt`, `txInterrupt`, `irq` |
| `uart_lsr`, `uart_isr`, `uart_isr_thri` | `lsr`, `isr`, `isrThri` |
| `uart_msr_idle`, `uart_msr` | `msrIdle`, `msr` |
| `uart_read`, `uart_write` | `read`, `write` |
| `uart_recv`, `uart_tx_pop`, `uart_rx_push` | `recv`, `txPop`, `rxPush` |
| `uart_acc` | `accepted` |
| `uart0_state`, `uart_mcr_reset`, `uart_divisor_reset` | `initial`, with MCR `0x08` and DLL `0x0c` |

The four FIFO/trace fields are `List (BitVec 8)`, registers are `BitVec 8`, and
MMIO offsets are `Int`. Source `Z.testbit (bv_unsigned b)` at nonnegative bit
indices is represented by `BitVec.getLsbD`. Byte masks, shifts, OR and bounded
register additions use modular byte operations; the source applies the integer
operation followed by `Z_to_bv 8`. Record updates replace positional state
reconstruction. The source's natural interrupt identifier is represented by
Lean `Nat`. These are representation choices, with no intended behavioral change;
they are not a machine-checked cross-prover equivalence certificate.

Preserved behaviors include:

- Both FIFOs remain sixteen bytes deep even with FIFO mode disabled, and receive
  interrupt readiness uses one byte rather than a configurable trigger level.
  These are deliberate abstractions in the paper model.
- DLAB redirects offsets 0/1 to divisor registers. Empty RHR reads return zero
  with FIFO mode enabled and otherwise return the retained RBR byte. Reading or
  clearing RX does not erase RBR.
- A full THR write drops the byte and still clears THRI. An idle IER write can
  arm THRI. ISR reads acknowledge THRI only when RX is not taking priority.
- FCR enable-bit changes clear both FIFOs, clear bits self-reset, and clearing TX
  arms THRI. The stored masks are IER `0x0f`, FCR `0xc9` and MCR `0x1f`.
- Internal receive on overrun drops the queue insertion but updates RBR. Host
  `rxPush` refuses a full FIFO instead. The host receive function has no extra
  loopback guard, matching the source.
- Transmitter completion always extends `out`; under loopback it feeds RX and
  preserves `wire`. Normal completion extends both. Modem input wiring under
  loopback and the idle MSR value `0xb0` are retained.
- Invalid register offsets return `none`. Writes to read-only LSR/MSR succeed
  without changing state, matching the source.

## Source proof mapping

| Source lemma | Location | Lean theorem |
| --- | --- | --- |
| `uart_read_lsr` | `DevModel.v:318` | `read_lsr` |
| `uart_read_total` | `DevModel.v:338` | `read_total` |
| `uart_write_total` | `DevModel.v:357` | `write_total` |
| `uart_recv_out` | `DevModel.v:393` | `recv_out` |
| `uart_recv_tx` | `DevModel.v:395` | `recv_tx` |
| `uart_recv_lcr` | `DevModel.v:397` | `recv_lcr` |
| `uart_tx_pop_acc` | `DevModel.v:443` | `txPop_acc` |
| `uart_rx_push_acc` | `DevModel.v:458` | `rxPush_acc` |
| `uart_read_stable` | `DevModel.v:473` | `read_stable` |
| `uart_write_thr_acc` | `DevModel.v:501` | `write_thr_acc` |
| `uart_dlab_of_lcr` | `DevModel.v:537` | `dlab_of_lcr` |
| `uart_tracked_of_fields` | `DevModel.v:544` | `tracked_of_fields` |
| `uart_write_1_stable` | `DevModel.v:555` | `write_1_stable` |
| `uart_write_0_dlab_stable` | `DevModel.v:567` | `write_0_dlab_stable` |
| `uart_write_3_stable` | `DevModel.v:579` | `write_3_stable` |
| `uart_write_2_stable` | `DevModel.v:593` | `write_2_stable` |
| `uart_tx_pop_out` | `DevModel.v:612` | `txPop_out` |
| `uart_rx_push_out` | `DevModel.v:621` | `rxPush_out` |
| `uart_write_out` | `DevModel.v:641` | `write_out` |
| `uart_tx_pop_dlab` | `DevModel.v:666` | `txPop_dlab` |
| `uart_rx_push_dlab` | `DevModel.v:676` | `rxPush_dlab` |
| `uart_write_lcr_0` | `DevModel.v:686` | `write_lcr_0` |
| `uart_write_dlab_0` | `DevModel.v:696` | `write_dlab_0` |
| `uart_tx_empty_of_out` | `DevModel.v:720` | `tx_empty_of_out` |

The additional exported theorems are:

`acknowledged_tx_quiet`, `fifo_clear_drops_accepted`, `fifo_toggle_example`, `idle_thri_acknowledgement`, `initial_status`, `irq_disabled`, `loopback_example`, `read_fields`, `read_isr_ack`, `read_isr_no_ack`, `read_rhr_empty`, `read_rhr_pop`, `recv_overrun`, `recv_rbr`, `recv_rx_bound`, `rxPush_fields`, `rxPush_full`, `rxPush_room`, `rxPush_wire`, `rx_priority`, `txPop_fields`, `txPop_last_thri`, `txPop_wire`, `write_thr_full`, `write_traces`.

The stronger field lemmas derive the source trace laws and additionally prove
wire preservation. The concrete examples establish board-reset status, two
successive ISR reads acknowledging THRI, loopback suppression of wire output,
FIFO-toggle flush and the fact that clearing queued TX bytes shrinks `accepted`.
No unrestricted write-monotonicity theorem is asserted; it would be false.

## Validation and remaining obligations

Commands, run from the repository with elan on `PATH`:

```sh
python3 tools/lake.py build MachCSL.Devices.Uart.Defs MachCSL.Devices.Uart.Proofs
python3 tools/lake.py env lean /tmp/xv6-lean-research/uart-axioms.lean
```

The owned modules compile with Lean 4.32.2. A transitive `#print axioms` audit of
all 49 public theorems reports only `propext` and/or `Quot.sound`; seven have no
axioms. There is no `sorry`, added axiom, `Classical.choice`, or native decision
axiom in those audited cones. The concrete examples use ordinary `decide`.
A source-name check verifies all 24 actual source lemmas have mapped exports.

No UART theorem declaration in the specified source section remains unported.
Comments mentioning other laws are not treated as extra existing declarations.
Remaining project work includes independent review, formal byte-representation
correspondence where required by the Sail interface, the width-checked device
bus wrappers, power/device thread integration, UART ghost resources and driver
proofs, and the observable accepted/wire trace theorem roots. None of these is
supplied merely by the pure model or its successful build.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
