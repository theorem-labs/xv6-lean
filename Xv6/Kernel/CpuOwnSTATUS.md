# Disabled CpuOwn resource layer

Status: **native implementation complete and frozen**. All seven approved pure fields and eighteen approved resource fields are proved. The six Lean modules build in **903 jobs**; the full physical/type/opaque/constructor audit passes **137 declarations**, with no exclusions. This is a resource layer, not a push_off/pop_off WP or a proof of boot-resource inhabitation.

Source pin: `.upstream/xv6iris` at `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The exact boundary and prerequisite inventory are in `docs/design/cpu-own-disabled-boundary.md`.

## Source and implementation mapping

| Source | Native implementation |
| --- | --- |
| `ProcGeom.v:765–799,934–945` CPU address/current process | `cpuPointer`, `procAddress`, `noffAddress`, `intenaAddress`, `curProc`; actual mycpu calculation reused |
| `TsoCtx.v:1055–1087` identity-tier word4 | `word4`, `word4_unfold`, `word4_access` |
| `IntrDefs.v:932–936` count eighth | `count`, using existing `SupervisorBits.countBit` at the actual era/hart name |
| `IntrDefs.v:951–1060` cells, CSRs, private state, hart bundle | `cells`, `hartCsrs`, `privateState`, `ownOff` |
| `CpuOwn.v:66–74,102–112` disabled branch/exclusivity | `open_own`, `exclusive` |
| `CpuOwn.v:146–165` disabled index agreement | `index_off`, using actual complementary eighth agreement |
| `CpuOwn.v:192–216` raw boot introduction | `init_boot` |
| `CpuOwn.v:227–326` CSR/set bounds, swap and process accessor | `csrs_access`, `size_le`, `zero_empty`, `locks_access`, `proc_access` |
| `IntrDefs.v:3582–3668` active count-token laws | `count_init`, `count_retune`, `count_push`, `count_pop`, `count_dec`, `count_pack` |

`CpuOwnDefs` retains actual identity-tier virtual-context noff/intena four-byte cells, the full eight-byte current-process field, `n < 2^31`, actual same-era/hart held-lock authority with `size ≤ n`, all four source CSR resources, and the existing SIE eighth. Base intena remains existential; positive-depth intena is pinned to the saved Bool. Positive-depth count is zero regardless of that Bool.

The active source removed the old count restore payload; the implementation follows the definition rather than the stale CpuOwn header. The actual CPU address is **0x800123e8 + 128*cpu**, proved from the existing machine-word mycpu expression rather than ProcGeom's stale header address.

`CpuOwnPure` proves all eight concrete hart address cases with ordinary kernel reduction, then modular field-address arithmetic/alignment and bounded unsigned/signed noff conversion and injectivity. `CpuOwnResources` proves seven Timeless instances, actual four-byte resource access and all count-only laws. `CpuOwnProofs` implements the full source bundle laws; exclusivity is derived from the actual full first noff byte even across different contexts/values. `CpuOwnLink` closes every native field and exports the concrete registry instance without caller-supplied component specifications.

The word4 accessor returns the same-context physical four-byte window and an internally funded replacement-value reconstruction wand. All four mapping claims and exact byte/timestamp fractions are retained. No eight-byte over-read, stronger alignment or assumed memory result is introduced. Count-token laws only reindex the eighth; they do not change noff/intena memory or claim a whole-bundle count update.

## Capacity and scope

The capacity reuses the existing execution/mapping/context/register/SIE components plus existing LockSet slot26. The SIE camera remains slot44 with `era.supervisorInterruptEnable cpu`; held authority is at `era.heldLocks cpu`. Registry equalities prove that execution, machine, bits and held-set witnesses are the same existing components. No new camera or runtime allocation.

`init_boot` consumes the actual empty held authority, a separate actual SIE eighth, actual noff/intena/proc cells and four actual CSR cells. It fabricates no canonical authority and does not infer ownership from zero-valued memory. Its conclusion is exact `ownOff ... 0 false process ∅`; the arbitrary intena and sscratch values remain existentially owned.

Enabled interrupt arms and trap/restore custody remain outside this layer. No context-migration law, CSR execution, width4 data-instruction WP, whole push_off/pop_off theorem, or boot name/cell installation is claimed. The positive-depth saved-enable=true branch remains expressible with its exact zero count eighth, without inventing a handler payload.

## Validation

```sh
PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.CpuOwnLink
PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/CpuOwnOwnerAudit.lean
```

Build passed **903 jobs** (Proofs 1.4s, Link 1.3s). Logs: `/tmp/xv6-lean-research/cpu-own-build.log`, `/tmp/xv6-lean-research/cpu-own-owner-audit.log`. Frozen hashes: `/tmp/xv6-lean-research/cpu-own-frozen.json`.

The audit checked all **137 physical-origin declarations in six modules**, including private/generated declarations, each axiom cone and complete type/opaque-body/constructor dependency traversal (`value? (allowOpaque := true)`). Only `propext`, `Classical.choice`, and `Quot.sound` occurred; no unsafe/partial dependency, zero exclusions. No sorry, new axiom or native decision tactic. No umbrella or other owner's production file was edited.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
