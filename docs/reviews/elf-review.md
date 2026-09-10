# Independent ELF reader review

Reviewed `Xv6/Elf/{Defs,Proofs,Kernel}.lean`, `Xv6/Elf/STATUS.md`, and the packed
image API against `iris/ElfFile.v` at paper commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The Codex artifact-audit agent reviewed
the coordinator's implementation before adding the separate packed coverage
bridge. This is a source and proof-boundary review, not a cross-prover equivalence
certificate.

No incorrect reader offset, field width, record order, table order, load filter,
or well-formedness condition was found in the implemented slice.

| Lean declaration | Pinned Rocq source | Review finding |
| --- | --- | --- |
| `read` | `elf_read`, `elf_avail`, `elf_le_at` | Both reject negative offsets. Empty reads succeed at every nonnegative offset, including beyond EOF. Positive reads require every requested byte. The difference between packed pages and contiguous lists requires coverage. |
| `Header`, `ProgramHeader`, `SectionHeader` | `elf_ehdr`, `elf_phdr`, `elf_shdr` | Same selected ELF64 fields in the same order; unsigned values represented in Lean `Int` preserve the source's `Z` arithmetic. |
| `parseHeader`, `parseProgramHeader`, `parseSectionHeader` | `elf_parse_ehdr`, `elf_parse_phdr`, `elf_parse_shdr` | All offsets and widths match. Full-width file fields must stay distinct from the narrower reads performed by xv6 code in `ElfEnc.v`. |
| `table`, `programHeaders`, `sectionHeaders` | `elf_table`, `elf_phdrs`, `elf_shdrs` | Same increasing table offsets and natural-number fuel; no reversal. |
| `loads`, `magicOK` | `elf_loads`, `elf_magic_ok` | Malformed tables produce no load segments; filter is exactly PT_LOAD = 1. Same six-byte class/endian/magic check. |
| `programHeaderWF`, `rangesDisjoint`, `loadsDisjoint` | `phdr_wf`, `range_disj_b`, `loads_disjoint_b` | Same range bounds, strict upper address bound, and empty-range disjuncts. |
| `wellFormed`, `sectionsWellFormed` | `elf_wf`, `elf_sections_wf` | Same structural conditions; section validity remains a separate predicate. Neither predicate claims that xv6's truncated code-side field reads can load every such ELF. |
| `Kernel.header`, `Kernel.load_segments`, `Kernel.loadable`, `Kernel.section_table_valid` | Concrete kernel specialization of the readers and structural predicates | Conclusions are proved by ordinary `decide` from actual imported packed constants. The expected header/segment literals occur as checked conclusions, not replacement assumptions. |

The pure proofs about negative and empty reads, table length, program-header
conditions and exclusion of overlapping ranges match their stated claims.
`Kernel.empty_rejected` checks a malformed input. None is an execution,
filesystem, loader or whole-system theorem.

## Representation bridge added after review

A bare `Packed` value can advertise a length whose pages are absent. Consequently
one cannot infer contiguous file availability merely from `byteLength` bounds.
`Xv6/Image/PackedProofs.lean` now makes the necessary hypothesis explicit:
`Packed.Covered image` means `byteLength ≤ pages.length * 4096`.

The module proves that every in-bounds page exists, defines a logical contiguous
byte list, and proves equality of partial packed lookup with list lookup at
**every** address under coverage. Finite sequences of reads agree as well;
bounded range reads equal the corresponding `drop`/`take` window, including the
executable `readBytes?` result. Padding and excess high page bits do not enter
in-bounds byte lookup. The logical list is not expanded to check the real images.
`Xv6/Image/Coverage.lean` proves coverage for both generated images using only
their extent and page count, and specializes the all-address lookup theorem.

Remaining obligations are explicit:

- Relate the packed constants to the original hex/byte inputs inside Lean. The
  coverage and lookup theorems alone do not prove this encoding equality.
- Relate the local natural-number little-endian assembler to the ported Sail
  assembler and compose the lookup bridge into the full `ElfFile` reader
  correspondence. The source deliberately uses one shared assembler.
- Port loaded file and zero maps, segment unions, read-only/writable geometry,
  and the correspondence with generated instruction/data maps.
- Establish filesystem executable-loading obligations, the loaded boot image,
  initial machine states and instruction semantics.

Validation: `lake build Xv6.Image.PackedProofs Xv6.Image.Coverage` succeeds with
Lean 4.32.2 (10 jobs). General proofs use kernel-checked tactics; actual coverage
facts use `unfold Packed.Covered; decide`, with no full-image list reduction.
A transitive `#print axioms` audit of all eleven new public theorems finds only
`propext` and/or `Quot.sound`; the two concrete coverage proofs have no axioms.
The five existing `Xv6.Elf.Kernel` roots each report only `propext`. No
`sorryAx`, `Classical.choice`, native decision axiom or new semantic axiom occurs
in these audited cones. The temporary audit driver was
`/tmp/xv6-lean-research/packed-bridge-axioms.lean`.
No root ELF file was changed by the reviewer.

## Subsequent implementation checkpoint

The remaining-obligations list above describes the review checkpoint. Since then,
`Representation.lean` has closed the full packed/list reader bridge and the
natural/integer assembler relation. `ImageRepresentation.lean` proves file,
zero-tail and ordered-union map correspondence. `ParserRepresentation.lean`
composes those results through header/table parsing to the complete list image.
All modules build and pass the project assumption/dependency audit. These are
within-Lean representation proofs; correspondence with raw hex, the generated
Sail assembler and instruction/data maps, filesystem loading and boot remains open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
