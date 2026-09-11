# Reservation mirror

This slice ports `iris/RiscvPtsto.v:1984–2071` at xv6iris `arxiv-v1`, commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. It uses the actual machine types:
CPU is Fin8; a reservation value is `Option Machine.Reservation`, whose snapshot
is the complete `ByteMap64`, including byte values and absent addresses.

| Source | Lean |
| --- | --- |
| `resv_map` | `resvMap`, a finite `Std.ExtTreeMap CPU Value` |
| `resv_map_lookup/insert/none/insert_id` | `resvMap_lookup/insert/none/insert_id` |
| `resv_auth_at` | `resvAuth`, full native ghost-map authority |
| `resv_frag` | `resvFrag`, full per-hart element ownership |
| `resv_any/intro` | `resvAny`, `resvAny_intro` |
| `resv_frag_agree/update` | `resvFrag_agree/update` |

The concrete map enumerates all eight CPUs. `resvMap_lookup` proves that each key
is present with `some (f cpu)`, so an unreserved hart is represented by
`some none`, never by an absent map entry. The lookup proof permits repeated
enumeration because the same CPU receives the same value; the actual enumeration
is the complete finite CPU list. Its extensional lookup meaning matches the
source's `map_imap` over `fin_to_set CPU`.

`resvMap_insert` tracks the actual machine `updateHart`, and `resvMap_insert_id`
proves the source's preserving case. `resvAuth_preserve` exposes that case as an
Iris equivalence requiring neither a per-hart fragment nor an update modality.
Changing a reservation requires full fragment ownership and full authority;
`resvFrag_update` returns both resources for the new value. The arbitrary-frame
version preserves the caller's resources. `resvAny_update` opens the existential
old value and performs the same checked update.

Native allocation exports the complete map's eight fragments. `allFragments_acc`
accesses any actual CPU unconditionally and supplies a reassembly wand. The
all-none allocation specializes this to the initial era shape. Capacities and
runtime names remain separate; allocation does not assume existing ownership,
an era record, a boot state, or a machine state interpretation.

`ReservationSpec.lean` imports definitions independently of proofs.
`ReservationLink.lean` instantiates the specification at the concrete registry.
Slot10 follows register6 and device7–9. The registry proves every slot below10
and at least11 unchanged and explicitly transports ledger, view, shared
mono-nat, history, register, and device capacities. The shared mono-nat remains
slot3; no second one is introduced.

Validation:

```sh
python3 tools/lake.py build MachCSL.Logic.ReservationLink
```

The Link module enforces a transitive axiom audit on all reservation declarations,
including generated/private helpers. Only propext, Classical.choice and Quot.sound
are allowed. No native evaluator, custom axiom, unsafe implementation or
placeholder is used.

Outstanding scope: the era/state interpretation must tie this authority to the
live global reservation function; instruction and scheduling rules must thread
or preserve fragments according to actual NodeStep behavior. This resource
bridge does not itself prove LR/SC semantics, reservation stability under other
agents' writes, or adequacy.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
