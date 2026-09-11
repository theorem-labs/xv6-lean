# Actual indexed mycpu fetch in supervisor Bare mode

Approved bounded contract, now implemented in the five modules below.
See `Xv6/Kernel/MycpuFetchSTATUS.md` for checked results. Source/model pin:
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; actual generated
`LeanPaperStock/Fetch.lean:212–284` and
`PlatformConfig.lean:2556–2561,2651–2654`.

The target is the actual `fetch ()`, at each of the fourteen concrete instruction
addresses, returning its exact `F_RVC` or `F_Base` result through a genuine native
WP. Compose the frozen `SupervisorBareFetch` boundary and native register/memory
lifting, retaining a single nine-cell footprint and the actual boot text window.
This is a Bare fetch theorem, not supervisor function execution or a KPT theorem.

## Owned modules and interface

Owned new files only:
`Xv6/Kernel/MycpuFetch{Defs,Spec,Plan,Proofs,Link}.lean` and
`MycpuFetchSTATUS.md`. Do not edit `SupervisorBareFetch`, the generic byte
resources, boot allocation, existing image/decoder certificates, or the generated
model. No camera slot is added.

Define `Shares` with `pc`, `misa`, and `bare : SupervisorBareFetch.Shares`.
Its exact footprint is:

```text
[(PC, pc), (misa, misa)] ++ SupervisorBareFetch.footprint bare
```

The nine distinct keys are PC, misa, mstatus, cur_privilege, satp, pma_regions,
pmpcfg_n, pmpaddr_n, and htif_tohost_base. Prove uniqueness; every read uses
its existing cell and returns it, rather than separating duplicate cells for
repeated reads. Fractions are explicit and unchanged.

Define the exact expected result:

```text
result i =
  if MycpuDecode.compressed i then
    F_RVC (BitVec.ofNat 16 (MycpuDecode.encoding i))
  else F_Base (BitVec.ofNat 32 (MycpuDecode.encoding i))
```

This is a fetch result, not a call to the compressed/base decoder. Existing
`MycpuDecode` theorems can later consume these encodings under their own exact
configuration/resource requirements.

The public pure configuration is:

- `rs PC = MycpuDecode.address i`;
- `_get_Misa_C (rs misa) = 1#1`, sufficient for the pinned Zca query; no full
  misa constant or unrelated extension restriction;
- `SupervisorBare.Config rs`: Supervisor privilege, SXL2, satp Bare; arbitrary
  satp ASID/PPN and no MPRV restriction for fetch;
- `SupervisorPmp.TorRam rs`;
- `rs htif_tohost_base = none`;
- an actual matching PMA region at the indexed address and actual width, with
  executable `override_PMA region.attributes PBMT_PMA`.

Prove the two/four width, actual-width physical alignment, RAM range, bit-zero
alignment and compressed classification from the existing concrete fourteen
image certificates. Do not require every PC to be four-aligned. The PMP/PMA/HTIF
premises remain real architectural facts, not a lower-level read result or
translation-correctness premise.

## Exact generated event sequence and decomposition

With the pinned RVFI configuration false and built-in extension hook, the
successful indexed fetch has this prefix:

1. PC twice for the extension check.
2. PC twice for alignment; `misa` once for Zca (through Ext_C).
3. PC once for the four-byte alignment decision; the actual Ziccif query is pure
   and true, as `MycpuFetchBytes.ziccif_enabled` already proves.
4. PC twice as the two `fetch_bytes` arguments.
5. The existing eleven `SupervisorBareFetch` register reads:
   mstatus, cur_privilege, mstatus, satp (translation);
   mstatus, cur_privilege (outer effective privilege);
   pma_regions, pmpcfg_n, pmpcfg_n, pmpaddr_n, htif_tohost_base.
6. The actual plain `readMem`, with the existing exact request metadata.

The eager Zca read is retained even at an address whose bit1 is zero. There are
nineteen actual register reads using nine cells. The result does not write PC,
any other register, or the reservation; the memory read advances the real view.

Prove a local concrete-word boundary using the existing
`SupervisorFetchRead.Boundary`:

```text
fetch_cut shares rs i config ... :
  ∃ tail,
    Boundary (footprint shares) rs
      (SupervisorFetchRead.request (MycpuDecode.address i)
        (MycpuFetchBytes.width i))
      (fetch ()) tail ∧
    (∀ tag, tail (Ok (MycpuFetchBytes.word i, tag)) = pure (result i)) ∧
    tail (Err ()) = Free.fail Exit
```

The success equality is intentionally for the actual owned word. For an
arbitrary two-byte word with low bits `11`, the genuine residual performs a
second fetch. A false all-words single-read theorem would delete this branch.
The boundary retains the original residual for every response; only its
actual-value success theorem discharges the extra-read path for these fourteen
instructions. The real tagged response possibilities and error Exit are kept.

Implementation can widen the frozen Bare-fetch register boundary to the unique
nine-cell footprint, prepend the exact register-only segment, and bind the
original result classifier. Its existing all-word `fetch_bytes` success law is
then specialized to the proved word, with ordinary kernel-checked bit/word
classification. No interpreter or oracle is introduced.

## Native contract and shared-span link

With the standard native world, machine capacity, generation certificate and
fixed trace/state interpretation already used by the existing memory WPs:

```text
wp_fetch shares rs i pureConfig image fixed whole gen era cpu ξ dq continuation post :
  genCertificate -∗ cells shares rs -∗ running ξ -∗
  contextWindow ξ (MycpuDecode.address i) (MycpuFetchBytes.width i)
    dq (MycpuFetchBytes.word i) -∗
  ▷ (∀ view, cells shares rs -∗ running ξ -∗ sameContextWindow -∗
       actualViewLB cpu view -∗
       WP (hart gen cpu (continuation (result i))) post) -∗
  WP (hart gen cpu (fetch () >>= continuation)) post
```

The native fold consumes the actual generation, nine register cells, running
context and byte window. Its read result follows from context ownership and
actual state interpretation at every allowed view. There is no public RAM
readability or state-preservation callback. The guard occurs at the actual
read; existing register lifting preserves the resources through the prefix.
The dead-generation behavior remains that of the already proved native rules.

`wp_fetch_shared` specializes to the actual
`MycpuBootResources.physicalSpan .discard`, using `discarded_context` and
`fetch_access`/`discarded_windows` to supply the indexed discarded window while
retaining the whole persistent span. It returns that span, the same nine cells,
running context and actual view receipt to its guarded continuation. No
fractional timestamp is created from a discarded receipt. A reservation-frame
corollary may expose the unchanged held reservation using the existing native
frame law.

The separate `Spec` records the main window and shared-span WP contracts;
`nativeSpec` discharges them from implementations. The approved boot allocation
already supplies this physical span; fetching still explicitly assumes the
stated Supervisor/Bare/PMP/PMA/HTIF configuration rather than claiming that
machine-mode cold boot is already in this supervisor state.

## Validation and remaining source work

Build all five new modules and audit every physical declaration plus all opaque
values, types and constructor dependencies. Allow only the standard three Lean
axioms. Use ordinary kernel proofs for finite indexed classification and word
normalization; no native decision procedure or generated semantics edits.

`CodeMycpu.v:39–92` gives the corresponding fourteen instruction-resource roots;
`KernelText.v:58–108` supplies their persistent text windows. This task connects
the actual physical window resource to actual fetch, but does not yet reproduce
those complete source `instr` assertions, static mapping/tier ownership, KPT
translation alternative, decoder/execution composition, or `mycpu` function WP.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
