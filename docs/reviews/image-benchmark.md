# Image proof representation benchmark

All measurements use pinned Lean 4.32.2, two Lean threads, the existing root dependency environment, and `/usr/bin/time`. Each individual command has a 30-second timeout. Proofs use ordinary `by decide`; **no native_decide, bv_decide, custom axiom or admitted successful theorem** was used. Failed elaborations produce Lean's usual diagnostic sorryAx but are explicitly failures and never accepted evidence.

## Original String representation

`Prefix.lean` asks for the four ELF header bytes by applying the repository's `decodeChars` to the first eight characters of `(Generated.kernelElfHexChunks.head!).toList`. This is tied directly to the actual generated image, not a separately typed header literal.

- maxRecDepth 2,000: fails in 0.38 s.
- maxRecDepth 20,000: fails in 1.08 s.
- maxRecDepth 100,000, 32 MiB thread stack: reaches the 30-second timeout, without a proved theorem.

Even first-byte access through `String.toByteArray` with bounds checking failed at maxRecDepth 20,000 (`ByteAccess.lean`).

A more direct prefix view **does** prove real bytes from the original image: `DirectPrefix.lean` projects `String.toByteArray.data.toList`, takes the first eight bytes, maps ASCII bytes to characters, and passes these to the existing `decodeChars`. Both its first ASCII byte theorem (`55`, hex character '7') and decoded ELF magic theorem (`[127,69,76,70]`) checked successfully:

- maxRecDepth 100,000, 32 MiB stack.
- 21.53 s total; maximum RSS 1,553,988 KiB (about 1.48 GiB).
- Both theorems have **no axioms** according to `#print axioms`.

This directly establishes a header prefix linked to `Generated.kernelElfHexChunks`. It is not a proof of whole-image decoding, and the alternate ASCII prefix projection has not been proved equivalent to the current UTF-8-decoding `String.toList` function for arbitrary input. The specific theorem itself is exact.

The poor performance follows a real reduction issue: Lean 4.32's String is UTF-8-backed and `String.toList` goes through full UTF-8 decoding; even projecting a small prefix from a large literal incurs substantial reduction/literal-construction work. Executable #eval speed is not a predictor of kernel proof cost.

## Packed Nat representation

`PackedShift.lean` tests actual pages 0, 1 and 69 of the paper's kernel, using `((page >>> (8 * offset)) % 256).toUInt8`. Page 1 is a full 32,768-bit nonzero Nat, so this is not merely a benchmark on sparse zero padding. Nine first/middle/last byte facts proved in 0.28 s total, maximum RSS 482,996 KiB. All nine proofs have no axioms. Earlier direct division-by-256-power prefix tests also passed, but shiftRight is preferable for high offsets.

`PackedAPI.lean` contains the **entire kernel** as 70 little-endian Nat pages and the proposed API in `Xv6/Image/Packed.lean`. It proves:

- Header reads of 4, 16 and 64 bytes.
- Individual bytes at offsets 4095, 4096, 8191 and 285559 (last byte).
- Out-of-range offset 285560 returns none.
- A two-byte read from the final byte returns none.

All nine checked in **2.76 s total**, maximum RSS **580,160 KiB**. The byte facts depend only on `propext`; ByteArray read facts on `propext` and `Quot.sound`. No sorryAx, native computation axiom or custom axiom occurs.

The temporary generator built Nat pages from the current generated image's exact hex bytes. This is the same untrusted-input-import boundary as the current hex generator. The packed arithmetic proofs do **not** assert a Lean-proved equivalence between the whole packed image and the original hex image; do not conflate the Python source correspondence with a kernel theorem. The separate original String-linked prefix theorem above supplies direct evidence for the existing representation.

## Minimal recommended API

See `Xv6/Image/Packed.lean` here:

```
structure Packed where
  byteLength : Nat
  pages : List Nat
```

- Fixed 4096-byte little-endian pages.
- `getByte? : Packed → Nat → Option UInt8` first checks explicit image bounds, then uses `pages[offset / 4096]?`, then shiftRight/modulo for the byte within that page.
- `readBytes?` rejects reads crossing the image boundary and missing pages, returning `Option ByteArray`.
- `getByte?_out_of_bounds` is proved generally.

There is **no fabricated zero fallback** for missing pages or offsets outside the declared byte length. Zero high bits within an existing Nat page are intentional page encoding; explicit `byteLength` prevents exposing last-page padding. A future well-formedness predicate can assert page-count coverage and absence of bits beyond the page size. It is not necessary to silently assume that predicate just to implement partial byte access.

Recommend making the packed image the canonical **proof-access representation** emitted by `tools/images.py`, while preserving raw hash/size/provenance and optionally the hex representation for readable extraction checks. Decode ELF headers/segments by bounded byte access; avoid repeatedly reducing an entire image into a ByteArray inside each proof. Use checked local lookup/header certificates and generic decoder-correctness theorems to compose the eventual loader proof.

## Scaling limits and next gate

These benchmarks prove byte access and bounded header reads only. They do not prove ELF validity, segment loading, kernel instruction decode, FS consistency or initialization. List page selection is linear in page index (70 pages for kernel, 500 for disk); assess indexed page tables if this becomes significant. ReadBytes currently repeats getByte per byte, so large reads scale with requested length and page-index traversal. Keep obligations page/block-local; do not use one giant `decide` over all 2,048,000 disk bytes. A complete packing/lookup invariant and generic ELF/filesystem parsers remain explicit work.

## Full disk page-index sample

`PackedDisk.lean` encodes all 500 pages of fs.img and proves byte observations at offsets 1024, 4096, 1000000 and 2047999, plus rejection at 2048000. The final byte query traverses the last page index, rather than only sampling the beginning of the image. All five facts checked in **6.62 s total**, maximum RSS **517,584 KiB**. Their only reported axiom is `propext`. The packed source was 1,807,013 bytes; zero pages naturally become the Nat literal 0. The recovered bytes hash to `77f42e2f20c0c2c72234dc9ea034f808a26a003f50e7bba62befe8c174bd07b5`, the pinned disk digest.

These are single-run measurements on the shared development host, including parsing/elaboration/import overhead; they are feasibility measurements, not statistically controlled performance comparisons. No claim of impossibility is made for the String representation: a direct String-linked prefix theorem succeeded, and other proved conversion lemmas or specialized reduction tactics may improve its costs. Packed Nat pages already provide a simpler measured path at the intended trust boundary.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
