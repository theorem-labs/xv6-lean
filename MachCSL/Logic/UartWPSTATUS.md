# Actual UART worker WP

`UartWP{Defs,Spec,Proofs,Link}` ports the invariant custody, observation
permits and native UART loop rule from pinned `WpUart.v:782–985` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The source-shaped ledger hooks
are included, not replaced by a machine-preservation assumption.

`uartBody` holds the actual era's UART client half and **all four** UART
ghost quantities from `UartGhost.ghosts`; `plicBody` holds the actual PLIC
client half and `PlicPlanOK` over every Nat context and enable word. Their
native invariants use explicit namespaces. Allocation consumes the actual
client half. `uart_initial_allocate` also allocates the four runtime UART
names and returns all source initial client resources; it works at any
actual UART state, including its actual DLAB value.

`obsPermit` matches source `uart_obs_permit`: an actual UART transition,
current trace shape and wire tie, the complete successor UART ghosts, and
history authority allow the history to move at the mask excluding the UART
namespace. `trivial_permit` discharges this contract using the invariant
that owns the other history half. `ledger_permit` implements source
`uart_obs_permit_ledger` with a timeless ledger, the exact TX hook (actual
pop, non-loopback, shape and wire agreement), and RX hook (actual push of
an arbitrary environment byte and shape). Both hooks run with the UART and
observation namespaces removed. Loopback TX and the silent arms preserve
the ledger without demanding an output hook. The namespace containment
premise is explicit; no conflicting invariant masks are silently assumed.

`uart_update` proves complete live machine/trace preservation for every
actual `UartStep`: TX updates the actual UART half and monotone output;
RX preserves the accepted/output/transmitter/DLAB ghost resources; latch
updates the PLIC half and proves its plan remains true; idle frames the
state. The actual machine transition restores trace alternation, generation
counts and the current era's UART wire tie. Durable disk preservation is
paid by the existing concrete `EraDevices` update theorems.

`wp_uart_loop` is a guarded native Iris `NotStuck` WP of the actual
`Machine.Expr.uart` worker with arbitrary postcondition. It considers every
actual next step and reconstructs the entire native state interpretation.
The live branch invokes the proved four-arm update; the stale-generation
branch uses exactly the source dead stutter and the guarded recursive WP.
There is no unproved successor-preservation callback, selected scheduler,
MMIO simplification or arbitrary live hart stutter. Trivial and ledger
wrappers discharge the permit in the two corresponding source settings.

The independent eight-field specification imports definitions rather than
the implementation. `registryUartWPSpec` and the concrete loop links use
`UartGhost.registry` (23 slots), explicit machine and UART capacities, and
explicit allocated native invariant names. Existing slots 0–19 remain
unchanged, UART slots are 20–22, and no new capacity is required by this
layer. Component specifications are discharged by their native proofs.

This completes the UART **worker** slice. Hart-side UART MMIO driver rules,
the combined production `dev_inv` and disk protocol, client-specific trace
ledger proofs, the full eleven-worker boot handler, and final system
adequacy remain separate work. In particular the trivial trace predicate
establishes custody, not the paper's end-to-end UART policy.

Validation: `python3 tools/lake.py build MachCSL.Logic.UartWPLink`
passes all 439 jobs (proof module 1.3 seconds, link 906 milliseconds).
`/tmp/xv6-lean-research/UartWPAudit.lean` independently collects the axiom
cones of all 216 UART WP and imported PLIC namespace declarations; only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. The earlier
UART ghost audit separately covers all 209 ghost declarations. No custom
axiom, `sorry`, `native_decide`, or `bv_decide` is used.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
