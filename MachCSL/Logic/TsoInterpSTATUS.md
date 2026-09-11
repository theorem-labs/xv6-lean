# Actual-state TSO era interpretation

The three `TsoInterp{Defs,Spec,Proofs}.lean` modules port the TSO conjunct of
`RiscvPtsto.v:2099–2148` at xv6iris arxiv-v1 commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, and its empty-log birth construction
in `RiscvAdequacy.v:890–900,1002–1039`. All assertions are native Iris `IProp`.

| Source | Lean export in `MachCSL.Logic.Tso.Interp` |
| --- | --- |
| `avf`, `avf_hart`, `avf_disk` | `avf`, `avf_hart`, `avf_disk`; `avf_device`, `avf_bound`, `avf_boot` provide useful generalizations |
| `tso_interp_at` | `tsoInterpAt`, with every original conjunct in source order |
| `dom TM = dom gmem` | `TimestampDomain`; `timestampDomain_iff_domainEq` proves equality of the corresponding domain predicates |
| `tso_interp_at_img` | `tsoInterpAt_image` |
| Pure `mm_ok` conjunct | `tsoInterpAt_memoryOK` |
| Authoritative timestamp lookup and `ts_ok` tie | `tsoInterpAt_timestamp_valid` |
| `(fun _ => (0, ts_pay_none)) <$> gmem` | `bootTimestamps`, with exact lookup, domain, and `TimestampMapOK` proofs |
| Fresh boot timestamp/log/log-length/view resources | `tsoInterpAt_alloc`, taking an explicit finite map and its exact memory equality |

`tsoInterpAt` existentially owns the full timestamp map and log-entry map,
asserts exact timestamp-domain equality and the complete `TimestampMapOK`,
asserts `History.LogRep`, owns full monotone log-length authority and total-Nat
agent view authority, and retains `MemoryOK g ∧ g.image = eraImage`. In
particular, non-hart agents receive log length, rather than an omitted/default
view. Every timestamp payload arm remains included in `TimestampMapOK`.

`Capacity` explicitly bundles the existing ledger, view, and history capacities.
`registryCapacity` derives them from the unchanged six-slot `History.registry`;
no new slots or global instance-search assumptions are introduced. `EraNames`
contains explicit runtime names. Native allocation supplies their ownership;
functor capacity alone never serves as an initialized resource.

The independent `InterpSpec` records image, memory, timestamp validity and
allocation entailments. `interpSpec` proves it for explicit capacities;
`registryInterpSpec` discharges capacity at the existing concrete partial
registry. Neither is advertised as the complete xv6 registry or machine safety.

Allocation starts from the actual `Machine.BootFacts`. Its core takes
`memory : AddressMap Byte` and `FiniteMap.decode memory = g.memory`. It returns
`tsoInterpAt` together with `byteInterpAt` (the full byte-map authority and exact
memory tie), every full byte-element fragment, every full timestamp-element
fragment, and the zero log-length receipt. Nothing converts writable bytes to
read-only ownership or discards the client maps. The timestamp payload is
exactly `payNone`; the log is exactly empty. `tsoInterpAt_alloc_finite` uses the
proved finite-address representation as a logical existential witness. Its
`encodeAll` argument must not be evaluated over the 64-bit address domain;
clients with a practical support map should use the core theorem.

The byte authority is explicitly the value component of source `gen_heap`,
separate from `tsoInterpAt`, as it is in the source era interpretation. Metadata
resources, register/device/reservation ownership, durable disk ownership,
fixed-versus-era composition, step preservation of this ownership interpretation,
WP rules and adequacy remain outstanding. The finite-map bridge does not
constitute a checked translation of Rocq `gmap` terms. The boot premise is the
existing exact machine predicate, without added image or reservation hypotheses.

Validation: `python3 tools/lake.py build MachCSL.Logic.TsoInterpProofs` passes
341 jobs; the changed proof module takes about 1.1 seconds. The exported
allocation and concrete registry contract were inspected explicitly. All 75 namespace declarations passed the full
axiom audit, recorded in `/tmp/xv6-lean-research/tso-interp-audit.log`.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; no native
proof evaluator, custom axiom, `sorry`, or opaque proof substitute is used.
The coordinator independently compared the definitions and allocation contract
against the pinned source and reported no changes required.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
