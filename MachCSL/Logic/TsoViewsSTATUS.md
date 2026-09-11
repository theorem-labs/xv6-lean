# Monotone views and log-length receipts

Implemented against `iris/TsoGhost.v` at paper pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. This slice covers every algebra and
receipt law in sections 1, 3 and 4. It supplies actual native Iris ownership,
allocation and frame-preserving updates; it does not yet install a machine
state interpretation or prove instruction rules.

| Source | Lean |
| --- | --- |
| `viewUR`, `vf`, `vone` (lines 36–41) | `TsoViewsDefs.ViewUR`, `vf`, `vone` |
| `vf_core_id`, `vone_core_id`, `vone_incl_vf`, `vf_local_update` (43–69) | corresponding `*_coreId` instances and same-named theorems |
| `llb`, persistence/timelessness, `llb_0/le/max/get/valid` (215–262) | `llb`, instances, `llb_zero/le/max/get/valid` |
| `view_lb`, persistence/timelessness, `view_lb_0/llb/le`, `vone_le_incl` (273–308) | `viewLB`, instances, `viewLB_zero/llb/le`, `vone_le_incl` |
| `view_auth`, allocation/fragment/validity/update (313–354) | `viewAuth`, `viewAuth_alloc/frag/valid/update` |
| `view_lb_get` (360–372) | `viewLB_get` |
| ambient `mono_natG` and Iris mono-nat laws | explicit `sharedNat` capacity, `natAuth`, `natLB`, `natAuth_alloc/update`, `natLB_le/get/valid` |

`ViewUR` is a total `Nat → MaxNat` camera, including all non-CPU agents.
Function equality is Lean extensional equality, which is the discrete OFE's
structural equivalence. Inclusion witnesses are explicit functions; coordinate
projection and local updates use native pointwise camera laws. The authority
owns both the full authority and same-valued fragment. A receipt owns a view
fragment plus a log-length fragment, or the paper's exact pure `bound = 0`
branch. No zero fragment is manufactured without the required update.

The source full-fraction `llb_get` and `llb_valid` specialize the proved Lean
laws, which additionally permit any native `DFrac`. `viewLB_get` retains the
source full-fraction signature and preserves both authorities.

The new `Views.registry` extends the existing two-slot ledger registry:

| Slot | Resource |
| --- | --- |
| 0 | unchanged byte-value map component |
| 1 | unchanged timestamp/pin map |
| 2 | authoritative total per-agent max-nat function |
| 3 | shared native mono-nat |

`registry_old` proves preservation of slots below 2; `registry_unused` proves
all slots at least 4 unchanged. Explicit `ElemG` witnesses derive both the new
`registryCapacity` and the old `ledgerCapacity` in this extension. These are
capacities, without runtime names or initialized resources. The existing
registry is not modified.

The source explicitly excludes a duplicate mono-nat from `tsoMemΣ` (lines
92–97 and 119–124). Slot 3 is the ambient shared mono-nat capacity, reusable
for independently named log lengths, context bounds and generations. Future
registry unification must reuse this slot or supply an explicit shared
`ElemG`; it must not silently allocate a second mono-nat functor. The native
`MonoNatG` record has an additional name field, so `Capacity.monoNat` adapts an
explicit runtime name locally. All actual ownership predicates pass the name
explicitly. Allocation's temporary adapter name is unused by the native
allocation implementation and does not restrict the freshly allocated name.

`TsoViewsSpec.lean` imports definitions only. Its `ViewsSpec` record exposes
actual Iris entailments independently of `TsoViewsProofs.lean`; `viewsSpec`
and `registryViewsSpec` prove and instantiate the contract.

Validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.TsoViewsProofs
```

The build checks 214 jobs; the two new proof-bearing modules take about one
second each. The entire new namespace is checked transitively by the audit
at `/tmp/xv6-lean-research/TsoViewsAudit.lean`, with its log at
`/tmp/xv6-lean-research/tso-views-axioms.log`; only `propext`, `Classical.choice`
and `Quot.sound` are allowed. No `sorry`, custom axioms, native decision
procedures or bit-vector decision procedures are used.

Outstanding source scope: log-message map resources; monotone dirty-set
resources and section 5's dirty-entry justification; metadata resources;
full `tsoMemG`/`tsoMemΣ` and final RISC-V registry unification; era names,
state interpretation, instruction rules and adequacy. No claim is made that
view authorities already track the running machine's current log or views.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
