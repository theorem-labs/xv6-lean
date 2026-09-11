# Native PLIC wire worker

`PlicWP{Defs,Spec,Proofs,Link}` ports the actual `WpUart.v:1425–1491` wire
worker over both pin cells on all eight harts. `wireCells` contains sixteen full
typed register fragments; `wireBody` existentially hides their values, and
`wireInv` gives them native invariant custody. Allocation consumes those actual
cells. The initial EventWP split exposes each pair without removing any other
CPU register resource.

`plic_update` handles both actual PlicStep constructors and every chosen hart.
It reads the driven value from the physical device state, opens only the wire
invariant, updates the selected authoritative register and its client fragment,
and restores the exact other fifteen cells. Full power interpretation including
durable disk, other registers, TSO, reservations and era registry is preserved.
As the source explains, the PLIC invariant itself need not be opened or consulted;
the source-interface wrapper retains that unused resource premise.

`wp_plic_loop` is the guarded native NotStuck WP, covering every live successor
and stale-generation stutter. Reducibility uses an actual supervisor-pin write
on hart zero, not a fabricated live idle rule. All transitions are silent and
preserve the observation interpretation using the actual machine step theorem.
The concrete 23-slot registry link supplies every component implementation.

Validation: complete 433-job target build passed. The independent physical-origin
and logical-cone audit and source review are recorded separately during integration.
No PLIC driver/MMIO rule, CPU cycle closure or complete boot handler is claimed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
