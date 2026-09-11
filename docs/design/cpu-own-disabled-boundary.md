# Disabled per-CPU ownership boundary

Proposed next checkpoint: `Xv6/Kernel/CpuOwn{Defs,Spec,Proofs,Link}.lean`, with narrow `Pure`/`Resources` helpers if needed. No implementation is asserted by this design. The first implementation checkpoint should contain compiler-checked Defs/Spec and stop for interface review.

## Executable source scope

Source pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. Read the complete `CpuOwn.v`; all `IntrDefs.v` count/cell/private-state/CSR definitions and count laws at 923–1060 and 3561–3673; the actual enabled-arm definition at 1980–1994; `ProcGeom.v` CPU-address/current-process definitions at 765–945 and the adjacent hart-tag boundary; `LockSet.v` actual authority/level definitions; and the virtual context-word tower in `TsoCtx.v:608–645,845–940,1055–1170` plus the final notation overrides. The source default tier in `Ktier.v` is KT0. `IntrDefsBase` and `ProcGeom.CurProc` do not bind a custom `CurKtier`, so these per-CPU memory cells retain the identity pin even when the executing capability is full tier.

Two stale comments must not drive the port:

- `CpuOwn.v`'s header mentions an old restore payload. Active `intr_count` is only the SIE ghost eighth. `IntrDefs.v:923–931,3561–3576,3643–3650` explicitly records removal of that payload; `trap_csrs` is held separately by clients who will re-enable interrupts. Positive-depth `eb=true` is therefore a legitimate disabled bookkeeping state with a zero count eighth; it does not establish a handler.
- `ProcGeom.v`'s header lists an older `cpus` address. The actual `mycpu_ret` calculation and pinned imported symbol use **0x800123e8**, already certified in the Lean mycpu modules. Addresses will reuse that calculation rather than the stale prose.

## Exact proposed definitions

Use a new capacity with only two components:

```lean
structure Capacity (GF : BundledGFunctors) where
  execution : MycpuRegimeShell.Capacity GF
  heldSets : LockSet.Capacity GF
```

Derive all register, context, mapping and SIE capacities from `execution`, so the SIE fragments agree with the existing disabled capability and the heap/context resources agree with the actual machine interpretation. The held-set component uses the already implemented disjoint-set authority, not a persistent ordinary-set camera. A registry instance pairs `MycpuRegimeShell.registryCapacity` with `KptGhost.heldSetCapacity` at existing slot26; SIE remains existing slot44. No new camera or runtime name.

Pure addresses preserve the exact source modular expressions:

```text
cpuPointer cpu = MycpuScalar.mycpuRet (HartTp.hartWord cpu)
procAddress cpu = cpuPointer cpu
noffAddress cpu = cpuPointer cpu + sign_extend64(120#12)
intenaAddress cpu = cpuPointer cpu + sign_extend64(124#12)
noffValue n = BitVec.ofNat 32 n
intenaValue eb = if eb then 1#32 else 0#32
medelegS = actual generated legalize_medeleg 0#64 0xffff#64
```

The resource predicates, with explicit same-era/same-hart names:

```text
word4 era ξ va dq value =
  pure(va.toNat % 4 = 0) *
  bigSepL (range 4) (j ↦ KernelDatum.byte execution.translation era
                                    identity ξ (addressAdd va j) dq (nthByte value j))

curProc era cpu ξ p =
  KernelDatum.word execution.translation era identity ξ (procAddress cpu) full p

count era cpu n eb =
  SupervisorBits.countBit execution.supervisorBits
    (SupervisorBits.namesOfEra era cpu) n eb

cells era cpu ξ n eb p =
  pure(n < 2^31) * word4 era ξ (noffAddress cpu) full (noffValue n) *
  (match n with
   | 0 => exists iv : BitVec 32, word4 era ξ (intenaAddress cpu) full iv
   | _+1 => word4 era ξ (intenaAddress cpu) full (intenaValue eb)) *
  curProc era cpu ξ p

hartCsrs era cpu =
  (exists sscr : BitVec 64, register sscratch full sscr) *
  register medeleg discarded medelegS *
  register mstateen0 discarded 0#64 * register sstateen0 discarded 0#32

privateState era cpu ξ n eb p held =
  cells era cpu ξ n eb p *
  LockSet.cpuLevel heldSets era cpu n held * hartCsrs era cpu

ownOff era cpu ξ n eb p held =
  privateState era cpu ξ n eb p held * count era cpu n eb
```

Here `register` always denotes actual `Registers.regPointsto` at `era.registers cpu`. `count` names `era.supervisorInterruptEnable cpu`; `cpuLevel` names `era.heldLocks cpu`. This is the exact `cpu_own ... false` branch. It does not define an enabled interrupt capability. The enabled index's pure formula alone would not supply the real enabled `sie_arm` resources and is unnecessary in this slice.

The original source `cpu_own` has no translation-tier parameter. The new `ownOff` likewise keeps static identity-tier fields, independently of the caller's execution tier. Using plain physical bytes in `cells` would drop its mapping/context obligations and is rejected.

## Proposed pure and native contracts

The small pure group should establish the certified per-hart address expression/range/alignment (Fin8, 128-byte stride), exact offset forms, and bounded `noffValue` injectivity/nonnegative signed range for `n < 2^31`. These are value/geometry statements, not ownership allocation.

The native Spec should expose the following source-backed rules, with exact signatures elaborated at the Defs/Spec checkpoint:

1. `open`/`close`: exact equivalence of `ownOff` with `cells * cpuLevel * hartCsrs * count`. This exposes the genuine cells needed by later stores; it does not change their values.
2. `init_boot`: consume actual full noff cell containing `noffValue 0`, arbitrary full intena cell, `curProc p`, a separate actual SIE off eighth, **actual empty held-set authority at `era.heldLocks cpu`**, and all four actual CSR cells, producing `ownOff ... 0 false p ∅`. Accept the source equality form for arbitrary supplied noff/medeleg values, or an exactly equivalent normalized corollary. It does not mint canonical authority or establish boot execution.
3. `exclusive`: two `ownOff` resources for the same era/hart contradict through their full noff byte ownership, even with different contexts, values or held sets. Derive from actual native byte validity; do not assume address disjointness.
4. `bound`, `size_le`, `zero_empty`: extract the count bound, held-set size bound and zero-depth empty-set fact while retaining the whole bundle.
5. `csrs_access`: return `hartCsrs` and its exact reassembly wand.
6. `proc_access`: expose the full `curProc p` cell and a wand accepting `curProc p'` to restore the bundle at p'. No assertion that p is a valid process pointer and no process-state/hart-tag ghost is added.
7. `locks_access`: expose the actual current authority and `held.size ≤ n`, with an arbitrary replacement-held-set reassembly wand requiring its actual authority and `held'.size ≤ n`.
8. `count_index_off`: actual off-capability eighth plus `ownOff` entails `(if n=0 then eb else false)=false`, returning both resources. A source `SieOffCapability.gpr` corollary extracts that eighth and restores the capability, if useful. In particular `n=0,eb=true` conflicts with the disabled capability; positive-depth `eb=true` is allowed.
9. Count-only laws from IntrDefs: boot-off identity; positive retune (any eb to either eb'); push with a separately owned zero arm eighth, yielding the source `n=0 → eb=false` fact and both eighths; decrement for eb=false; interior decrement at depth≥2; positive packing. These reindex only the count token. They must not be presented as updating the noff/intena cells or whole `ownOff` for free.
10. `word4` alignment/byte unfolding and identity physical-window accessor with a replacement-value wand. The accessor retains all four actual mapping claims and the same context; it returns the actual generic four-byte `TsoContextBytes.window`, not a word/read-success assumption. This is the narrow missing memory wrapper needed for subsequent actual lw/sw rules.

Timeless instances should cover the complete resource components. The exclusive bundle must not be declared persistent. Native implementations should discharge existing component Specs in Link; no public resource-restoration callback or new axiom.

## Minimal dependency gaps and subsequent work

The cameras and runtime names already exist. `SupervisorBits.countBit`, its `countIndex` law, and exact fractional agreement cover the SIE choreography. `LockSet.cpuLevel` and its native laws cover the actual name-keyed held authority and size coupling. KernelDatum already provides the exact virtual context byte and eight-byte word. **The missing first-layer wrapper is the four-byte virtual context word**, which can be defined locally and proved from four existing byte resources without replacing them by a full eight-byte cell or changing alignment. Source CPU-field address aliases and the four-CSR bundle are also not yet exported as a native component.

For the initial boot-resource theorem, all premise resources remain real inputs. Existing era allocation does not by itself establish S-mode `medeleg`, install SIE ghost names or allocate the canonical empty held-set authority. A future combined boot producer must allocate/install these names and carve the actual data bytes once. This design does not infer those resources merely because their values are zero.

The next push_off implementation will additionally need actual width4 data-load/store instruction wrappers and integer signed-count branches; current width8 data wrappers and width2/4 fetch wrappers do not supply those contracts. The generic physical context bytes and memory-event rules are reusable, but no four-byte instruction WP is claimed here.

Full context migration (`cpu_own_morph`) requires actual native context-dominance transport for each virtual byte; that transport is not currently exported by the KernelDatum/context interface. It is explicitly outside this first disabled resource checkpoint rather than replaced by arbitrary reindexing. Similarly, enabled SIE arms, handler fixed points, trap CSR payload/claim custody, reenabling pop_off and scheduler transfers remain separate work. The source's active count definition does not require those pieces inside `count`.

No source definition, existing owner file, umbrella or generated semantics is changed by this design.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
