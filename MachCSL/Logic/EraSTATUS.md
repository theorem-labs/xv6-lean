# Era allocation and fixed state interpretation

`EraDefs` represents all24 fields of the paper's `riscvEraGS`, including
the kernel-layer runtime names. Its interpretation contains all seven
conjuncts of `RiscvPtsto.v:2149–2159`: global registers, full native heap,
devices, per-era disk image, TSO, reservations, and reservation validity.
The finite era image is tied to the actual machine image by the proved decoder.

`Era.allocate` constructs these assertions from actual `BootFacts` and a
finite-map representation of machine RAM. It attaches metadata to the existing
byte authority, preserving the byte camera/name shared with TSO. It returns all
initial register cells, byte and timestamp fragments, log receipt, metadata
tokens, device halves, disk range and reservation fragments. The eleven kernel
auxiliary names are retained from an explicit template; no ownership for their
unimplemented resources is claimed. Thus this is not the full kernel
`power_boot_res` initialization.

`EraSpec` states this contract independently; `EraProofs` imports component
specifications only. `EraLink` supplies proved implementations and discharges
the contract for registry slot15. The registry contains complete immutable era
records, with full authority and persistent discarded fragments.

`MachineInterp.powerInterp` retains sized durable-disk authority outside the
powered-on conditional. Its registry domain is exactly the number of starts.
`generation_cases` proves that a certified generation is either dead or live;
`live_era_access` selects precisely its registered era and returns a restoration
wand. `power_off` advances the death counter while preserving the fixed disk and
registry. `power_on` allocates from actual boot facts, preserves the current disk,
registers the new era, and returns its persistent certificate and all machine
client resources. `initial_off_alloc` allocates the fixed resources, whole disk
client range and observation client from an actual observation-consistent state.

`StateInterpSpec` independently states these five laws. The actual native Iris
instance uses the same image-parametric machine language and future trace, with
zero extra laters and a trivial fork postcondition. `InvariantLink` separately
allocates native invariant resources; it records that native adequacy still
consumes one step credit per machine step.

Build: `python3 tools/lake.py build MachCSL.Logic.StateInterpLink` passes
(406 jobs). Full native resource allocation is now available. Hardware-step
ownership preservation, WP lifting, initial thread WPs, kernel auxiliary
resources and machine adequacy remain open. These laws alone establish no
whole-system safety theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
