# Independent era and state-interpretation review

Result: no correction required for the declared definition/composition scope.
Reviewed `MachCSL/Logic/EraDefs.lean`, `EraRegistry.lean` and
`StateInterpDefs.lean` against `iris/RiscvPtsto.v` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. This review reads the source
record, component definitions and Iris instance; it does not review the
concurrently developed `StateInterpProofs.lean` or claim transition lifting
or adequacy.

`Era.Record` preserves all 24 fields of `riscvEraGS` (175–381), in source
order. Per-hart names remain total functions on the actual eight-element
`CPU`; parked-hart and process-state names remain total Nat-indexed
functions. Kernel-map/table/bound, supervisor translation/SIE/SPP/SPIE,
process, log-mirror and held-lock fields remain present even though their
client resources are not allocated by these definitions. The record is
independent of the Iris functor family and contains no Iris proposition.
Its image is a finite 64-bit physical-address byte map.

| Source `RiscvPtsto.v` | Reviewed Lean correspondence |
| --- | --- |
| `era_memGS_of` (533–536) | `heapInterpAt` reconstructs the complete native gen_heap from the era's value and metadata names |
| `disk_dur_interp` (636–638) | Era's unsized `Disk.imageAuth` tied to the actual Virtio disk |
| `era_registered`, `gen_cert` (641–650) | Native discarded registry fragment and exact born/started/registered certificate |
| `disk_fixed_auth` (720–721) | Sized disk authority at the fixed name and fixed size |
| `gregs_interp_at`, `dev_interp_at` (2083–2091) | All-hart register interpretation and all three device halves |
| `tso_interp_at` (2126–2140) | Existing complete TSO interpretation, with names projected from the era and decoded era image |
| `era_interp` (2149–2159) | All seven source conjuncts in `Era.interp` |
| `power_interp` (2173–2180) | Counter pair, fixed durable authority, full registry authority/domain and conditional current-era interpretation |
| `obs_interp` (2192–2196) | Exact past/future history, observation well-formedness and history half through `PowerGhost.obsInterp` |
| `riscv_irisGS` (2218–2224) | Actual native `IrisGS_gen`, zero later steps, `True` fork postcondition and step/thread-index independent interpretation |

The extra finite-map existential around the heap is a checked representation
bridge to the production machine's partial-function RAM. Its equation is
exact at every address. Existing `FiniteMap.decode_encodeAll` proves that
every such function has a finite-map witness, and `decode_injective` rules
out representation ambiguity. This does not execute the enormous exhaustive
64-bit encoder or establish a cross-prover theorem about Rocq `gmap` itself.

Capacity coherence is structural. The TSO ledger is projected from the heap
capacity, so its byte authority uses the same camera; the era heap name is
also used by its ledger name projection. Generation/start/log-length reuse
the same existing mono-nat capacity. The disk capacity is shared by the fixed
and per-era disk authority; their runtime names remain explicit. Native Iris
ownership, rather than an assumed naming inequality, constrains simultaneous
full ownership.

`RegistryDomain` states pointwise presence exactly at generations below
`startCount`, the extensional meaning of `dom R = set_seq 0 count`. It does
not permit missing prior eras or extra future entries. The powered-on branch
requires a lookup of the current generation and that exact full era's
interpretation. The powered-off branch is source `True`. The fixed durable
disk authority stays outside that branch, so it is not discarded with the
era. Grouping the two counters introduces only separation-conjunction
association relative to the source.

`Era.registry` adds a native ghost map from Nat to the **complete** era record
at slot 15. Explicit equalities preserve slots 0–14 and all slots above 15.
Value equality includes all record fields; no truncated era or arbitrary
replacement equivalence is introduced. The native invariant capacity is
still an explicit `InvGS_gen` argument to `irisGS`; these 16 application
slots alone are not presented as a closed adequacy precondition.

The current `MachineInterp.Capacity` and `FixedNames` are the projection
needed by the state interpretation. They are not the full source
`riscvFixedGS` interface (383–521): auxiliary kernel cameras, crash/trace
client predicates, swap name and their invariant contracts remain separate
work. The whole observation trace is an explicit argument. Merely
constructing these records or the native Iris instance neither allocates the
resources nor proves a WP, a power-on initialization, or kernel safety.

Independent validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.StateInterpDefs
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/StateInterpDefsAudit.lean
```

The definition target builds successfully (369 jobs). The second command
independently audits 180 public/private era and state-interpretation
namespace declarations, rejecting every transitive axiom other than
`propext`, `Classical.choice` and `Quot.sound`. It also compiles explicit
coherence equations for the heap/TSO byte capacity, shared mono-nat capacity,
heap name, and finite-map existence. Output:
`/tmp/xv6-lean-research/state-interp-defs-independent-axioms.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
