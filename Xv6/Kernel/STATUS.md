# Pinned kernel maps

The byte maps and metadata are imported from `mit-pdos/xv6iris` tag `arxiv-v1`,
commit `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The imported kernel software
retains its copyright and permission notice in `LICENSES/xv6-riscv.txt`.

`tools/kernel_maps.py` reads the actual `kernel-rocq/KernelInstrs.v`,
`KernelData.v`, and `KernelSyms.v`. It verifies the checkout revision and compares
every input byte to the pinned Git blob, records SHA256 and Git blob hashes,
strictly parses each chunk, and follows the map's actual `List.concat` reference
order. It rejects malformed entries, missing/repeated chunks, modified source,
out-of-range bytes, or changed pinned counts. It does not create source maps from
the ELF. The ELF comparison is an additional independent check.

The import retains 23,748 code bytes, 17,884 data bytes, all 8,607 instruction
records (index, integer address, bit width, encoding), 222 symbol definitions and
original ELF-name aliases, entry/extent/rodata-boundary constants, the ordered
segment metadata, and seven allocated sections. Section metadata comes from the
source comment emitted by `tools/dump_elf.py`; it is distinguished from Rocq
`Definition` metadata. Symbols retain their Rocq names and original ELF names.

The concrete byte representation is 13 ordered page-bounded runs. Each run records
an integer base address, an explicit byte length, and the little-endian integer
formed only from its source-list bytes. Compression preserves order, duplicate
precedence, zero bytes, and absent addresses. `ByteRun.entries` expands these runs
back to their ordered address/byte lists. `runMap_eq_listMap` proves first-entry
lookup semantics for arbitrary runs, including overlaps and duplicate addresses.
The pinned importer additionally checks that the actual source keys are unique.
It never extends a sparse source map by defaulting a missing address to zero.

The kernel-checked results are:

- `fileBytes_eq_fileImage`: the left-biased union of the independently imported
  source code/data maps equals `Elf.fileImage Images.kernel` at every integer
  address, including addresses outside the file-backed domain.
- `fileBytes_union_bss`: adding exactly `Elf.zeroImage Images.kernel` produces
  `Elf.loadedImage Images.kernel`. File-backed coverage is 41,632 bytes; the
  zero tail extends to `0x800235c8`.
- `code_loaded` and `data_loaded`: either source map's successful lookup is the
  corresponding byte in the loaded ELF.
- `code_defined_iff`, `data_defined_iff`, and `code_data_disjoint`: exact sparse
  domains and disjointness. Code occupies `[0x80000000,0x80005ba0)` and
  `[0x80006000,0x80006124)`; data occupies the complementary file-backed regions.
- `entry_parsed`, `segments_parsed`, `sections_parsed`: entry, all dumped program
  header fields, and numeric allocated-section geometry/flags/file-presence agree
  with the actual ELF parser. The section header flags, rather than the one RWX
  program header, identify the first writable section at `0x8000a264`.

The byte proof checks 13 arithmetic packed-page slice equalities, then uses a
proved truncation/shift lemma for every byte within each slice. It does not test
41,632 examples or trust Python's comparison as a theorem. All 13 slice proofs
compiled together in approximately 0.4 seconds in the initial build; the full
initial correspondence module also compiled in approximately 0.4 seconds.
`Audit.lean` enforces the foundational-axiom allowlist across every theorem in the
kernel-map namespace and generated certificates, including helper theorems. Its
regression facts check duplicate precedence, both sparse holes, BSS absence from
the file-byte map, and the actual entry byte. No native evaluator, placeholder
axiom, `sorry`, or `native_decide` participates.

Reproduce and check:

```sh
python3 tools/kernel_maps.py .upstream/xv6iris --check --self-test
python3 tools/lake.py build Xv6.Kernel.Audit
```

Omit `--check` to regenerate the six `Xv6/Generated/KernelMaps*.lean` files.
The machine-readable input provenance is embedded in `KernelMapsProvenance.lean`.
The importer regression checks exercise reversed chunk order, duplicate keys,
sparse runs, malformed entries, omitted/repeated/unknown chunks, malformed
comments, and invalid byte values.

Remaining obligations: the source-imported symbol names/addresses have not been
proved equal to a Lean parser of the ELF symbol/string tables, and section names
have not been proved equal to parsed section-name strings. The 8,607 imported
instruction records are metadata; their full Sail decode/execution theorem
library and the kernel program proof remain to be ported. The source-to-Lean
importer is untrusted and reproducible, not itself a verified Rocq parser.
This module proves image correspondence, not kernel safety or whole-system
adequacy. Raw-hex decoding versus packed-image correspondence is supplied by the
separate `Xv6.Image` work; no new assumption for that equality is introduced here.

The newer [symbol occurrence certificate](SymbolSTATUS.md) checks all 222
imported original ELF names and values against their actual linked symbol/string
table rows, including complete mycpu and cpus entries. The older numeric metadata
proofs above do not perform that parsing themselves. Occurrence does not assert
equality with nm's filtering or duplicate-name selection.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
