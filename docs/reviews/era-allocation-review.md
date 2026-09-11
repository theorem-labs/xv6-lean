# Independent era-allocation and registry review

Result: no correction required for the declared machine-era scope. Reviewed
frozen `EraDefs`, `EraSpec`, `EraProofs`, `EraRegistry`,
`EraRegistryProofs` and `EraLink` against paper-pinned `RiscvPtsto.v`
and the PowerOn allocation in `RiscvAdequacy.v:842–950` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. This extends the previous
record/state-definition review. Concurrent `StateInterpProofs` changes are
outside this review.

The complete 24-field era record and all seven source `era_interp`
conjuncts remain intact. `EraSpec.allocate` takes actual `BootFacts image g`
and an exact finite-map representation of the actual RAM. It does not take
initialized ownership as a premise. Its result includes the newly assembled
era, the image equality, preservation of the eleven auxiliary fields, all
seven machine-owned era conjuncts and every fragment in `Era.bootClients`.

The implementation discharges those resources through six explicit
component contracts:

- Complete per-hart register authority and all 180 typed initial register
  cells for each of eight actual CPUs.
- TSO byte/timestamp allocation, empty log authority, zero log-length
  authority and all-agent views for the actual boot state.
- Full native gen_heap with metadata, constructed by attaching metadata to
  that existing byte authority at its existing name.
- Actual UART, PLIC and Virtio states, each with a machine half and a
  returned client half.
- A fresh unsized per-era disk-image authority at the actual total disk,
  with the entire `[0,diskBytes)` fragment.
- All eight actual optional reservation snapshots and their fragments;
  actual boot facts supply the pure reservation invariant.

The byte authority is allocated exactly once. `Heap.attachMetadata` uses
the shared ledger capacity and retains the value name; it adds only the
metadata map and per-location metadata tokens. The resulting heap owns the
same finite memory that the timestamp domain describes. Both its exact
RAM-decoding equation and the TSO image equation are retained when the
record is assembled. Reading `Heap.attachMetadata` and its finite-map
induction confirmed that it does not substitute a separately allocated
value authority.

The returned client bundle is deliberately stronger than the corresponding
machine portions of the source's `power_boot_res`: it keeps full register
files instead of an arbitrary requested register subset, metadata tokens
that the source allocation discards, and the zero log-length receipt. This
adds usable ownership rather than changing the machine interpretation.
The timestamp, byte, device, disk and reservation client resources remain
present. Future source register-subset consumers can restrict the complete
supply through its checked accessors.

`assemble` replaces exactly the machine-owned fields and image while
preserving the eleven kernel-layer fields stated by `AuxiliarySame`.
These template names are data, not assumed allocated tokens. Consequently
this theorem is **not** the complete source `power_boot_res` (441–576):
kernel-map/table/bound tokens, supervisor bit/translation ghosts, process
and held-lock resources, log-mirror custody/swap resources, client-lent
resources, crash invariant and generation certificate remain separate
allocation/lifting work. The fixed durable-disk authority is correctly
outside this per-era allocator. It neither consumes nor recreates old-era
fragments.

The registry uses native full authority and discarded persistent fragments
over Nat keys and the complete era record. `registry_alloc`, lookup,
record agreement and fresh insertion/persistence match the native source
operations at `RiscvPtsto.v:641–650` and
`RiscvAdequacy.v:906–912`. Agreement compares the entire record; there is
no arbitrary relation identifying distinct era images or auxiliary names.

The independent specification imports only component definitions/contracts.
`EraProofs` receives those contracts explicitly. `EraLink.contracts`
discharges all six using the actual native implementations for the supplied
capacity; `registryEraSpec` closes the contract at the explicit slot-15
registry. No unproved component specification remains in that linked root.
The operational boot facts and memory representation remain explicit pure
premises, as stated; allocation does not prove a power-thread WP.

Independent validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.EraLink
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/EraAllocationAudit.lean
```

The 398-job build passes. The separate audit checks all 167 public/private
era-namespace declaration cones, including the linked implementation, and
accepts only `propext`, `Classical.choice` and `Quot.sound`. Output:
`/tmp/xv6-lean-research/era-allocation-independent-axioms.log`. No production
file was changed by this review.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
