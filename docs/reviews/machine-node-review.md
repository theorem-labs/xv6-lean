# Independent byte-memory, node and boot review

Reviewed `MachCSL/Memory/Bytes.lean` and
`MachCSL/Machine/{Node,NodeProofs,Run,BootProgram,Platform}.lean` against the
paper's `arxiv-v1` artifact, commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
No source-transcription mismatch was found in the inspected rules. This is a
source review plus checks of the stated Lean properties, not a cross-prover
simulation theorem or closed-machine gate.

## Byte writes and maps

[`RiscvModelBytes.v:write_bytes`](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/RiscvModelBytes.v#L217-L219)
uses right-fold insertion over byte offsets in ascending order. `writeBytes`
retains that order, modular address arithmetic, and little-endian byte extraction.
If an access wraps around the address space, the first byte wins an address
collision. No size or no-wrap premise is silently imposed. `snapshot` and
`Footprint` match the source snapshot map and footprint set extensionally.

**Correction to an initial review comment:** the address domain is `BitVec width`,
which is finite. Consequently, an arbitrary `ByteMap width` cannot have infinite
support. The outstanding obligation is a checked representation bridge to the
source finite-map library; there is no additional-state problem arising from
infinite support. Reservations have the same finite address domain.

`writeBytes_overlay`, `flat_writeBytes`, `snapshot_domain`, and
`writeBytes_preserves_submap` state useful write/log/reservation facts without
adding access-size assumptions. Independent kernel `decide` checks of a
five-byte write across a two-bit address space confirm both the collision winner
and an adjacent byte; no native evaluation shortcut was used.

## Hart-local and sequential execution

The reference is [`RiscvLang.v:mnode_step`](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/RiscvLang.v#L799-L945).
The reviewed Lean relation preserves these source details:

- Registers update only the register file. Completed MMIO accesses update only
  the device state; writes also clear the reservation.
- Every ordinary RAM read chooses one common view between the current view and
  log length. Fetches and page-table walks take this same monotone-view arm.
- A blocked exclusive read keeps its computation and clears its reservation;
  a blocked write keeps both computation and reservation. Neither consumes an
  event response. These are conditional blocking rules, not arbitrary stuttering.
- Successful exclusive reads use flat memory, set the view to log top and record
  their snapshot. RAM writes update memory and append the corresponding message;
  exclusive writes advance past that append and plain writes preserve the view.
- Exactly the four source W-to-R fence kinds drain. Restart chooses a Boolean
  tick, begins the actual generated cycle, and clears the reservation.
- The absent-payload write-event branch is rejected. The corrected generated
  builtin returns pure `Ok None` before such an event is emitted, matching the
  source builtin; this rejection is not an interpretation of that pure return.

`node_flat_preserved` establishes the flat-memory/write-log invariant for one
hart node. `node_view_monotone` correctly requires the explicit initial bound
`view ≤ log.length`; an exclusive read otherwise could lower an invalid view.
Neither theorem claims the complete global memory/reservation invariant.

`Run` is a finite completed free-event execution under the source's auxiliary
sequential handler. Its RAM reads use the flat byte memory, barriers are state
no-ops, choices range over their result carrier, and failure/discard cannot
resume. `run_bind` proves exact decomposition through an intermediate result
and state. It does not replace sub-instruction CPU interleaving by whole-instruction
atomic execution.

The `Bus Device` argument is still explicit and generic. Its concrete device
fabric, access-width checks and autonomous device transitions must be supplied
before these relations describe the intended system. This parameterization is
visible in the definitions and is not a completed machine instantiation.

## Board initialization and physical-memory attributes

`boardWired` and `boardRegisters` retain the order and values in
[`ArchReset.v:233–275`](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/ArchReset.v#L233-L275):
reset-address wiring and hart ID, then the PMA table and the explicit register
writes. `bootProgram` invokes actual generated `init_model` and
`init_boot_requirements`; it does not prepend simulator initialization or replace
reset by a literal post-reset register table. The vector is an explicit parameter;
the source paper specializes it to `0x80000000`.

Rocq's `boot_prog` uses `init_model_at "" plat_hook`. Its checked source split
lemma connects this to `init_model` because the overridden cancellation hook is
pure unit. The generated Lean runtime has the same local hook realization, but
this review does not supply cross-backend equality of the initializer bodies.
An actual boot run and reset postcondition remain necessary.

All PMA attributes and the three ordered regions match
[`RiscvLang.v:pma_boot*`](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/RiscvLang.v#L1061-L1137):
ROM at `0x1000`, the IO band at `0x2000000`, and RAM from `0x80000000` to
`0x88000000`. The RAM atomics, reservation support, PTE flags and 16-byte
misaligned-atomicity granules are retained. Defining the table alone does not
prove its validation by the generated initializer or access checks.

## Follow-up: register evaluator and non-vacuous boot witness

Source review of `RegisterRun.lean`, `ColdBoot.lean` and `Boot.lean` found no
mismatch in the stated scope. `registerRun` has explicit finite fuel, handles
only register events, and returns `none` for every unsupported event. Its
soundness theorem constructs an actual finite `Run` trace and keeps memory and
devices unchanged; evaluator success is not assumed to establish concurrent
machine execution.

`ColdBoot` uses one all-default initial register file as a non-vacuity witness,
then runs the actual generated board/reset/firmware program. Its theorems quantify
over arbitrary reset vectors and hart IDs. `BootFacts` still existentially permits
arbitrary initial register files, matching the source boot predicate, so this
one witness does not narrow the allowed boot states. PC and misa checks concern
the actual run output. The image byte function remains an explicit parameter;
the witness alone does not connect that function to the paper ELF.

`BootShape` preserves the old generation and resets the old Virtio control state
while retaining its disk, matching the source rule where PowerOff already
increments the generation. `boot_memory_ok` and `boot_reservations_ok` establish
the declared boot invariants. Compiled validation of this follow-up is pending
the root's boot-module build; the earlier validation below covers the original
six reviewed modules.

## Remaining correspondence and validation

The representation obligations from the [Sail correspondence audit](../Sail-correspondence.md)
remain: source `N`/`Z` widths, bitvectors and finite maps, dependent registers,
register-access metadata, and unconstrained source natural/range choices.
`GetCycleCount` uses natural zero where the source returns integer zero; a
result/continuation bridge is still required. The reviewed arms do not resolve
these by silently selecting narrower choices.

All reviewed modules were imported successfully on Lean 4.32.2. The independent
check also reran the wrapped-write examples and inspected the axioms of
`node_flat_preserved`, `node_view_monotone`, `run_bind`, `bootProgram`, and
`pmaBoot`. Only standard Lean axioms occur; no custom axiom or native proof
shortcut was introduced. This validation supports the stated local results,
with the generic bus and remaining correspondence premises explicit.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
