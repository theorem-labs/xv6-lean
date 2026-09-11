# One allocation of the actual mycpu fetch bytes

Approved bounded design, now implemented by the five modules listed below.
See `Xv6/Kernel/MycpuBootResourcesSTATUS.md` for checked results. Source pin:
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

Extract the 34 distinct physical bytes at `0x800018ba` once from the byte and
timestamp clients of an actual xv6 boot. Preserve both exact deleted-map
remainders. Sharing happens after this extraction; it never extracts fourteen
overlapping full-ownership windows from the original map.

## Source and existing dependencies

`BootCarve.v:154–211,1220–1255` splits existing byte/timestamp clients and
persists timestamp-zero elements. `KMap.v:217–238` adds the static executable
mapping claim, positive canonical address, and tier pin when constructing the
source `text_pointsto`. `KernelText.v:58–108` obtains overlapping instruction
windows from discarded, persistent, hart-independent text ownership.

The proposed slice implements the physical ownership part of that construction.
It does not yet define the source `kernel_text`, `text_pointsto`, `instr_bytes`,
KPT mapping claims, or tier pins. Those additional source resources cannot be
replaced by a physical address equality.

The existing checked dependencies are:

- `MycpuFetchBytes`: all 34 actual ELF/RAM bytes, all fourteen exact fetch
  footprints and words, and their union covering the span.
- `BootWindow.extract_stored`: native byte/timestamp client extraction with
  modular-address uniqueness and exact deleted-map remainders.
- `Era.allocate` and `Era.contracts`: actual native allocation of the full
  machine-era interpretation and all boot clients.
- `TsoContextBytes`: matching-fraction context windows, fractional splitting,
  persistence, and linear subwindow access/reassembly.
- `TsoRead.pristine_window_mint`: explicit persistence of existing full
  timestamp-zero elements, with no second allocation.

The four-byte aligned fetch footprints depend on the pinned enabled
`Ext_Ziccif`; `MycpuFetchBytes.ziccif_enabled` proves that fact about the actual
model. This body has no uncompressed instruction on the split two-plus-two
fetch path. The last four-byte fetch reads `0x11018082`, including `01 11`
immediately after the 32-byte function body. Several earlier footprints also
overlap. The resource footprint is consequently 34 unique bytes, rather than
the sum of the fourteen fetch widths.

## Owned files and definitions

Owned new files only:
`Xv6/Kernel/MycpuBootResources{Defs,Spec,Proofs,Sharing,Link}.lean` and
`MycpuBootResourcesSTATUS.md`. No changes to frozen generic window, physical
fetch, boot, model, or code-sharing modules; no new camera slot.

Use namespace `Xv6.Kernel.MycpuBootResources`. The generic resource parameters
are the existing `TsoStore.Capacity` and `TsoStore.Names`; the final link uses
`Era.Capacity` and the actual era names. Define:

```text
address = BitVec.ofInt 64 MycpuDecode.base
spanWord : BitVec (8 * 34)
  = little-endian assembly of MycpuFetchBytes.bytes, converted UInt8 → Byte
keys = BootWindow.keys address 34
rawSpan c names = TsoStore.storedWindow c names address 34 spanWord 0
remainder c names memory =
  mapBytes c.heap.ledger names.tso.ledger.bytes (deleteKeys memory keys) *
  mapTimes c.heap.ledger names.tso.ledger.timestamps
    (deleteKeys (Tso.Interp.bootTimestamps memory) keys)
contextSpan c names ξ dq =
  TsoContextBytes.window c names ξ address 34 dq spanWord
physicalSpan c names dq =
  TsoRead.byteWindow c.heap.ledger names.tso.ledger.bytes address 34 dq spanWord *
  TsoRead.pristineWindow c.heap.ledger names.tso.ledger.timestamps address 34
fetchWindow c names ξ dq i =
  TsoContextBytes.window c names ξ (MycpuDecode.address i)
    (MycpuFetchBytes.width i) dq (MycpuFetchBytes.word i)
```

`spanWord` is a proof/resource packaging device, not an actual 34-byte machine
request. The actual requests remain the existing two/four-byte fetch events.

## Extraction and actual allocation signatures

The following summarize the agreed mathematical interfaces; the separate
`Spec` and its `nativeSpec` link now provide their checked Lean contracts. All pure memory premises of the generic extraction are
discharged from real boot/image facts in the specialized wrappers.

```text
extract_initial (facts : BootFacts Xv6.Machine.bootImage g)
    (decoded : FiniteMap.decode memory = g.memory) :
  mapBytes ... memory * mapTimes ... (bootTimestamps memory)
    ⊢ rawSpan c names * remainder c names memory

boot_resources facts decoded :
  Tso.Interp.bootClients capacity.tso era.tsoNames memory
    ⊢ rawSpan ... * remainder ... memory * natLB ... era.logLength 0
```

Prove the 34-byte word-byte correspondence, RAM bounds, address uniqueness,
actual boot map lookups, and boot timestamp lookups. Prove both remainder
lookups equal their original maps at every address outside `keys`.

Define `otherClients` by retaining all the other conjuncts of `Era.bootClients`:
all initial register cells, every heap metadata token, device fragments,
the sized durable-disk bytes, and all reservation fragments. A full-client
wrapper returns these unchanged together with the extracted span, exact
remainders, and log-length-zero receipt.

The actual allocation wrapper is:

```text
allocate_boot (before : Machine.State) (template : Era.Record) (diskBytes : Nat) :
  let g := Xv6.Machine.boot before
  let memory := FiniteMap.encodeAll g.memory
  ⊢ |==> ∃ era,
    ⌜era.image = memory ∧ Era.AuxiliarySame era template⌝ *
    Era.interp capacity era g * rawSpan ... * remainder ... memory *
    natLB ... era.logLength 0 * otherClients capacity era memory g diskBytes
```

This invokes the existing native `Era.allocate` with the actual
`Xv6.Machine.boot_facts before`, then consumes its client resources through
`extract_initial`. It does not replace an authority for an already allocated
era. `FiniteMap.decode_encodeAll` supplies the representation equality with no
caller premise. `encodeAll` is the existing finite-domain logical witness,
whose 64-bit enumeration must never be evaluated. The generic extraction is
also available for any practical finite map with the proved decode equality.

No new native invariant-world allocation or full power-loop theorem is part
of this wrapper. Kernel auxiliary names are preserved exactly as
`Era.AuxiliarySame` specifies; corresponding kernel tokens are not invented.

## Two explicit sharing paths

1. Matching fractional context ownership:

   ```text
   rawSpan ⊢ contextSpan ξ (.own 1)
   contextSpan ξ (.own (q1 + q2))
     ⊢ contextSpan ξ (.own q1) * contextSpan ξ (.own q2)
   contextSpan ξ dq
     ⊢ fetchWindow ξ dq i * (fetchWindow ξ dq i -∗ contextSpan ξ dq)
   ```

   The generic `TsoContextBytes` rules split both byte and timestamp ownership
   together. The concrete accessor uses the proved offset/width bounds and
   exact subword byte equality. It preserves the entire span through a linear
   reassembly wand. Successive overlapping accesses may use that restored
   span; no simultaneous full-owned overlapping-window bundle is exported.

2. Source-style physical text sharing:

   ```text
   rawSpan ⊢ |==> physicalSpan (.own 1)
   physicalSpan (.own (q1 + q2))
     ⊢ physicalSpan (.own q1) * physicalSpan (.own q2)
   physicalSpan dq ⊢ |==> physicalSpan .discard
   physicalSpan .discard ⊢ contextSpan ξ .discard
   physicalSpan .discard
     ⊢ [∗list] i ∈ List.finRange 14, fetchWindow ξ .discard i
   ```

   The first update explicitly persists the existing timestamp-zero clients.
   Fractional physical bytes can then share that persistent timestamp resource.
   Persisting the bytes makes the whole physical span persistent and
   hart/context independent. This legitimately supplies all overlapping windows
   and arbitrary CPU/context instantiations, retaining the shared span as well.

   Fractional physical bytes plus discarded timestamps do **not** silently
   become context bytes at a requested owned fraction. The conversion above is
   specifically at `.discard`. No timestamp-fraction upgrade or reminting is
   used. The matching-fraction path remains available before persistence.

## Validation and scope

Build the five owned modules and audit every physical declaration and its full
opaque-value/type/constructor cone. Only the existing standard three Lean
axioms are allowed. Small concrete byte/arithmetic certificates use ordinary
kernel checking; no evaluation of the full memory encoder is permitted.

The result establishes allocation, exact framing, and native ownership of the
actual physical bytes. Using those resources for the entire supervisor mycpu
fetch still requires the source Bare/KPT translation alternatives and the
remaining mapping/tier resources. It proves neither the mycpu instruction WP
nor whole-kernel safety by itself.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
