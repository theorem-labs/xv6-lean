# Supervisor aligned physical-access prefix

Implemented and frozen for independent review in `SupervisorPhysicalDefs`,
`SupervisorPhysicalProofs`, and `SupervisorPhysicalPlan`. This is the bounded
first step in `docs/design/supervisor-translation-boundary.md`.

The actual generated `pmaCheck` returns `Ok ⟨CannotSplit, 0⟩` under an exact
matched-region, selected permission-field, and alignment hypothesis. Supported
calls are fetch widths 2/4 with no reservation, PTE load width 8 with either
reservation flag, and ordinary data load width 8 with no reservation. All
unrelated region attributes and registers remain arbitrary. The proof retains
the real one `pma_regions` read, the data-load assertion, and pure MAG decision.

`priority_aligned_plan` proves the actual successful
`check_pma_with_pmp_priority` branch, which does not read PMP. `htif_none_plan`
retains the actual HTIF read; `mmio_ram_plan` includes eager CLINT/signature/HTIF
evaluation and returns false from mathematical RAM interval bounds plus the
disabled HTIF value. The pinned platform has CLINT enabled at `0x2000000` with
size `0xc0000`, and signature support disabled. `device_ram` separately proves
the real node-level device guard false from the same RAM lower bound.

`physical_check_plan` composes the existing exact supervisor TOR entry-zero
proof with the PMA proof for actual `phys_access_check`: PMP reads configuration,
configuration again, and addresses, then PMA reads its table. This is the
PMP-then-PMA API; the separate checked-memory-read API first uses the priority
wrapper. No RAM read event or result is assumed or proved here.

All plans use native `RegisterPlan.Returns`, with explicit arbitrary fractions
and footprint membership. Singleton PMA and HTIF corollaries expose the minimal
footprints. Native `RegisterPlan.fold` can consume these proofs with its usual
generation certificate, unique footprint ownership, and continuation; this
slice introduces no camera, allocation, memory-preservation callback, or new WP
axiom. The TOR configuration retains arbitrary later entries and irrelevant
entry-zero bits through the previously reviewed supervisor PMP layer.

Source mapping at xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:

| Lean result | Source boundary |
| --- | --- |
| `ReadGrant`, matched region premise | Needed projections of `RiscvFetchExec.v:100–164` PMA contract |
| `RamRange`, RAM classification | `RiscvExtras.v:600` positive RAM interval; source CLINT/signature/HTIF exclusion helpers |
| `pma_aligned_plan`, `priority_aligned_plan` | `SmodeCorePt.v:1321–1347`, `hfrun_check_pma_ifetch_S`; physical PTE permission branches in `SmodePte.v:336–504` |
| `physical_check_plan` | Actual generated `Mem.lean:385–390`; existing source `SmodePte` TOR grant |
| Actual event ordering | `Mem.lean:262–402`, `Pma.lean:349–426`, `Platform.lean:219–253,703–711` |

This does not port the full source `pma_allows_all` predicate: source integer
width quantification, broader write/atomic/misaligned guarantees and their
generated Nat-domain correspondence remain separate. The matched grant used
here is the exact positive-width projection required by these calls, not a
claim about denial of other accesses. Complete physical RAM reads, PTE A/D
updates, Bare/Sv39 translation, mixed-width instruction fetch, and mycpu WP
remain outside this prefix. No full-state preservation or kernel safety theorem
is asserted.

Validation:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Machine.SupervisorPhysicalPlan`
  passed 443 jobs; final plan module approximately 1.1 seconds.
- `/tmp/xv6-lean-research/SupervisorPhysicalAudit.lean` independently enumerated
  all 58 physical-origin logical declarations across the three modules,
  including private helpers and generated constructors. All axiom closures use
  only `propext`, `Classical.choice`, and `Quot.sound`. The dependency walk
  includes declaration types, opaque bodies with `allowOpaque := true`, and
  inductive constructor types. No unsafe/partial semantic dependency and no
  excluded runtime companions. Output is in `supervisor-physical-audit.log`.
- No `sorry`, custom axiom, `native_decide`, `bv_decide`, generated-model edit,
  or code outside the owned prefix was used. The design's aligned-fetch prose
  was separately corrected at the coordinator's request to retain the actual
  pinned `Ext_Ziccif` query and its enabled definition.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
