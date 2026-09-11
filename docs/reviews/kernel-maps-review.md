# Independent review of the pinned kernel maps

Reviewed `tools/kernel_maps.py`, all seven `Xv6/Kernel/*.lean` modules, generated
map/certificate structure, pinned `KernelInstrs.v`, `KernelData.v`,
`KernelSyms.v`, and the relevant pinned `tools/dump_elf.py` definitions.
Baseline: `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

Result: no semantic correction required for the declared scope. A misleading
comment on `fileBytes_outside` was reported to the owner: a sparse hole in one
source map is filled by the other, so the theorem describes addresses outside
the combined file-backed interval, including BSS. The theorem itself is correct.

The importer checks HEAD, lock revision, working-source equality to each pinned
Git blob, counts, instruction indices/widths, byte ranges and map-domain
properties. Chunk parsing follows the actual `List.concat` reference order.
It preserves first-entry-wins semantics rather than sorting references or using
last-write dictionary conversion. The actual pinned maps have unique keys and
are mutually disjoint. Explicit byte-run lengths preserve trailing zero bytes;
page splitting and discontinuities do not fill holes. This remains an untrusted,
pinned-format importer, not a verified parser for arbitrary Rocq programs.

The independent checks passed:

- `python3 tools/kernel_maps.py .upstream/xv6iris --check --self-test`.
- Reexpanded compressed runs reproduce every ordered source tuple: 23,748 code
  bytes and 17,884 data bytes, with exact address/value/order equality.
- All 8,607 source instruction encodings agree with the corresponding little-
  endian source bytes, and all have the source-required four-byte fetch window.
  These are host checks, not new instruction decode/execution theorems.
- Direct Lean compilation of `/tmp/xv6-lean-research/KernelMapsFreshAudit.lean`
  checks the fresh correspondence, metadata and regression proof bodies against
  their compiled dependencies. Its enforced 157-theorem dependency audit admits
  only `propext`, `Classical.choice` and `Quot.sound`. Log:
  `/tmp/xv6-lean-research/kernel-maps-independent-audit.log`.

The formal chain is sound within that import boundary. `ByteRun.lookup_eq_listMap`
and `runMap_eq_listMap` establish ordered first-winner lookup, including duplicate
and overlapping runs. The arithmetic slice theorem proves every byte from one
packed-page certificate, respecting both the explicit run length and image bounds.
The 13 actual certificates use ordinary kernel-checked `decide`. Exact domain
coverage plus successful-byte agreement yields `fileBytes_eq_fileImage` as
function equality, including negative addresses and addresses outside the file
interval. `fileBytes_union_bss` adds exactly the parser's zero tail; `data_loaded`
uses the checked source-map disjointness before selecting the right side of the
left-biased union.

The domains match the source: code has two regions, data fills the complementary
file-backed intervals, and their union is `[0x80000000, 0x8000a2a0)`.
The source allocated-section permission comment is decoded as ELF section flags
(ALLOC=2, WRITE=1, EXEC=4), not program-header flags. `sections_parsed` checks all
numeric allocated-section fields and file-presence information against actual
section headers. `entry_parsed` and `segments_parsed` connect the source metadata
to the real parsed entry and program headers; the writable boundary is
`0x8000a264`.

Limits are accurately documented: imported instruction records are not a Sail
decode library; symbol names/addresses and section names have no Lean ELF
string/symbol-table parsing correspondence yet; no kernel instruction safety,
state interpretation or whole-system adequacy follows from these maps. The
source-to-Lean parser is reproducible and checked against pinned files but is
outside the kernel theorem. The separate raw-hex/packed-image proof remains the
responsibility of `Xv6.Image` and was not duplicated here. I did not run a Lake
build touching Images while the other agent owned its encoding build.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
