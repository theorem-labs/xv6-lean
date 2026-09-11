# Actual full mycpu fetch, supervisor Bare mode

Implemented and owner-frozen for independent review. Five modules:
`MycpuFetch{Defs,Spec,Plan,Proofs,Link}.lean`. Source pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

`wp_fetch` proves a native WP for actual generated `fetch ()` at every indexed
mycpu instruction address. It returns the exact `F_RVC` or `F_Base` encoding
through the continuation. `wp_fetch_shared` obtains the actual word from the
new boot-allocated discarded 34-byte span and retains that entire span.
`nativeSpec` discharges the separate public contracts without subordinate WP,
readability, translation-correctness, or state-preservation oracles.

The one nine-cell footprint contains PC, misa, mstatus, cur_privilege, satp,
pma_regions, pmpcfg_n, pmpaddr_n, and htif_tohost_base, with explicit arbitrary
fractions. Uniqueness and length are proved. Repeated reads reuse their cell
sequentially; all nine cells return unchanged. The successful path follows all
nineteen actual generated register reads:

1. PC, PC for the extension hook.
2. PC, PC, misa for alignment and the eager Zca/Ext_C check.
3. PC and the pure, pinned-enabled Ziccif query.
4. PC, PC as the actual `fetch_bytes` arguments.
5. mstatus, cur_privilege, mstatus, satp for Bare translation.
6. mstatus, cur_privilege for the outer effective privilege.
7. pma_regions, pmpcfg_n, pmpcfg_n, pmpaddr_n, htif_tohost_base before the read.

The actual RAM event uses the existing exact plain request, including its
metadata. The running context and same window return with the real chosen-view
receipt. No register or reservation write occurs in this path; there is no
separate reservation premise in the public rule. The guarded continuation is
paid through the existing actual native memory rule, including its established
dead-generation behavior.

`Config` has only the actual indexed PC, misa.C=1, Supervisor/SXL2/satp-Bare,
TOR RAM, disabled HTIF and a matching executable PMA region. Concrete width,
physical alignment at that width, and RAM bounds are proved from the actual
fourteen addresses. No four-alignment premise is imposed on all instructions,
no full misa constant is required, and fetch has no MPRV restriction. PMA and
supervisor configuration remain caller facts; cold boot is not claimed to have
already switched to this supervisor state.

The `FixedRead` boundary retains the full original residual for every response.
Its immediate success equality is proved only for the actual owned word,
including every returned tag. This distinction preserves the genuine second
fetch on an arbitrary two-byte response whose low bits are `11`. The checked
mycpu words prove that this branch is not taken for these fourteen addresses.
The error response's actual `Exit` is retained. No generic all-word single-read
claim is made for `fetch ()`.

The existing `SupervisorBareFetch.fetch_boundary` supplies the complete Bare,
PMP/PMA/HTIF physical prefix, widened to the unique nine-cell footprint. The
new register prefix and suffix retain the generated free program. The native
`SupervisorFetchRead.Boundary.fold` obtains the result from actual context byte
ownership. No new interpreter, memory evaluator, allocation, camera slot,
generated model change, or timestamp-fraction upgrade is used.

Source mapping:

| Source/model | Checked scope |
| --- | --- |
| `LeanPaperStock/Fetch.lean:212–284` | `isRVC`, actual fetch branches, repeated PC reads, real residuals and exact result |
| `PlatformConfig.lean:2556–2561,2651–2654` | Pure Ziccif and one real misa read for Zca/Ext_C |
| `SupervisorBareFetch` and its reviewed source mapping | Actual Bare translation, outer privilege and physical read |
| `CodeMycpu.v:39–92`, `KernelText.v:58–108` | Corresponding fourteen concrete encodings and shared physical footprints; complete source instruction assertions remain separate |

This proves fetch, not decoding or executing the returned instruction, the
mycpu function WP, static mapping/tier ownership, KPT translation, or
whole-kernel safety. Existing decoder certificates keep their own exact
configuration requirements for later composition.

Validation:

- `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.MycpuFetchLink`
  passed 622 jobs. Final Plan 1.4s, Proofs 1.0s, Link 827ms, no warnings.
- Fresh full physical-origin audit passed all **83 declarations** in the five
  modules, including private helpers and constructors. Traversal includes all
  types and opaque values plus inductive constructor dependencies;
  `collectAxioms` runs on every declaration. Zero excluded roots, no
  unsafe/partial logical dependencies, only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Evidence: `/tmp/xv6-lean-research/MycpuFetchAudit.lean` and
  `/tmp/xv6-lean-research/mycpu-fetch-{build,audit}.log`.
- No `sorry`, custom axioms, native decision procedures or frozen dependency
  edits. Concrete classifier checks use ordinary kernel proofs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
