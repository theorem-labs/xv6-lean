# PLIC wire-worker review

Codex independently reviewed `PlicWP{Defs,Spec,Proofs,Link}` against `WireInv.v` and `WpUart.v:1416–1491` at source pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, the actual `Machine.PlicStep`/`Step` constructors, and the linked physical register update. The semantic/resource review passes. One unnecessary callee-proof import was identified and a replacement checked separately before integration.

The wire body has both full typed pin cells for every member of the actual eight-hart set. Its existential total functions retain every possible bit value. Allocation consumes those sixteen cells. `wire_access` extracts the selected pair and reconstructs the other seven pairs using the exact finite-set deletion fact; after either arm, one selected pin changes and the other fifteen cells retain their resources.

Both `PlicStep` constructors use the value calculated from the physical device state, exactly as in the source. The supervisor arm writes `sig_seip` from the supervisor context and the machine arm writes `sig_meip` from the machine context. `power_write_register` updates the authoritative register and its matching full client fragment while returning the complete power interpretation, including the other harts, memory, devices, reservations, TSO state and era registry. The source explicitly explains why no PLIC ghost agreement or opening of the PLIC device invariant is needed: the actual transition already supplies the physical device state. The source-shaped wrapper retains its unused PLIC-invariant premise.

The native NotStuck WP uses guarded recursion, establishes reducibility with a real hart-zero supervisor-pin transition when live, and analyzes every actual live successor (both arms, arbitrary hart). The stale/inactive-generation branch follows the actual dead-thread stutter. Every arm emits no observations or forks; the live case transports observation interpretation with the actual `Step` witness. The mask is restored before opening the wire invariant, and the full state interpretation is reconstructed for the successor. This is an infinite device-worker WP, not a driver/MMIO theorem or an assembled machine adequacy result.

The concrete link uses the common 23-slot UART/PLIC registry. The recorded physical-origin audit covers all 24 logical declarations, private helpers included, with only `propext`, `Classical.choice`, and `Quot.sound`, no unsafe/partial logical dependency, and no excluded runtime companions.

Import review: the original `PlicWPProofs` imported `RegisterWPProofs` without using a register-WP theorem. Its physical update is supplied by `EraStateLink`; native lifting is supplied by `Iris.ProgramLogic.Lifting`. A read-only copy tested the direct imports to avoid importing the callee WP implementation. No production file was edited by this reviewer. Probe: `/tmp/xv6-lean-research/PlicWPImportProbe.lean`, log `plic-wp-import-probe.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
