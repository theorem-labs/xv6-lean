# Kernel ELF symbol parser and certificate peer review

Result: **PASS after the parser owner corrected compressed-section handling**.
The independent reviewer read all five frozen Lean modules, the generator, and
the relevant original export code. The reviewer did not author those modules
or edit their proofs. The reviewer authored `tests/KernelSymbols.lean` and this
report. Source baseline is xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

Reviewed files: `Xv6/Elf/SymbolDefs.lean`,
`Xv6/Kernel/Symbol{Defs,Proofs,ImageProofs}.lean`,
`Xv6/Generated/KernelSymbolCertificates.lean`, and
`tools/symbol_certificates.py`. The conclusion is selected uncompressed ELF64
row occurrence for every imported symbol, not a complete ELF validator or
equivalence with `nm`'s selection, ordering, or deduplication.

## Layout, bounds, and the correction

The ELF64 symbol offsets and widths are correct: name 0/4, info 4/1, other 5/1,
section index 6/2, value 8/8, size 16/8. ELF64 section link is 40/4 and entry
size is 56/8; the reused section parser supplies the preceding fields.
These agree with the [gABI symbol layout](https://gabi.xinuos.com/elf/05-symtab.html)
and [section layout](https://gabi.xinuos.com/elf/03-sheader.html).

`symbolAt` requires the ELF magic, class 64, little-endian encoding, ordinary
64-byte section headers, an in-range selected table index, `SHT_SYMTAB`,
24-byte entries, complete table payload bounds, size divisible by 24, and an
in-range row. With nonnegative row indices, the row-start test and divisibility
also ensure the whole 24-byte entry is inside that payload. Mathematical
`Int`/`Nat` arithmetic prevents machine-word index overflow. It follows the
actual `sh_link` to an in-range `SHT_STRTAB`, checks its payload bounds, and
requires the name offset to lie inside it. The string offset's conversion to
Nat cannot silently truncate a negative offset after these checks.

`readCString` stops at the first zero byte and fails on exhausted extent or a
missing packed byte. Its fuel is exactly the remaining declared string-table
extent. Suffix names and the empty name are allowed, consistent with byte-indexed
string lookup; a terminator outside the table cannot finish a name. Names are
raw byte lists, not decoded text. See the
[gABI string-table description](https://gabi.xinuos.com/elf/04-strtab.html).

The initial parser ignored `SHF_COMPRESSED`, which would interpret compressed
section data as raw symbols or strings. The reviewer reported this; the owner
added rejection of bit `0x800` on both selected sections. The final tests
exercise both guards. This is required because compressed payloads have their
own header and interpretation under
[gABI section compression](https://gabi.xinuos.com/elf/03-sheader.html#compressed-sections).

The parser intentionally does not verify the entire section-header table or
every ELF validity rule. Unused declared headers may extend past the file;
the regression suite records that selected-row parsing still succeeds in that
case. It does not check version, alignment, section overlap, every reserved
field, first/last string-table zeros, or the semantics of every symbol type.
It requires ordinary section counts and `SHT_SYMTAB`; extended section counts
and dynamic symbol tables are outside its accepted format. Extended symbol
section indices remain raw. A zero name offset is read from the bytes, so
acceptance on a malformed string table is not a theorem that the whole table
obeys ABI naming conventions. These limits do not undermine the concrete
checked row-occurrence claim.

## Imported names, certificate, and final theorem

The pinned `tools/dump_elf.py:489ff,1090ff` invokes the selected `nm`, keeps
lines matching its address/type/name regular expression, selects the first
occurrence of each name, sorts by value, and—in the Rocq exporter—sanitizes
identifiers with collision checking. The new certificate does not reimplement
or prove that algorithm. It checks the previously imported original ELF name
bytes and value against a concrete table row, additionally requiring nonzero
`st_shndx`.

The witness generator checks the exact source revision, source files against
their committed versions, and the pinned raw image length/hash. It extracts
all 222 source definitions and alias comments, finds a unique candidate row
per name/value, and emits row indices. UTF-8 decoding and its additional
uniqueness checks are untrusted witness-generation choices: the Lean checker
compares actual raw parsed bytes against each imported name's UTF-8 bytes and
rechecks the value and section-index condition.

`all_rows` uses ordinary `decide` for all indices in `Fin 222`. `all_imported`
separately proves that the actual imported list has length 222, converts any
membership witness to a bounded index, handles failed row lookups by
contradiction, and uses the proved `check_iff` to obtain the actual row.
Consequently the final theorem covers every member of that list, not a sample
or an assumed generator list. It does not prove that the rows exhaust the ELF
symbol table, that the mapping is unique, or that `nm` would choose them.

The separate literal certificates identify `mycpu` at table 18, row 141,
value `0x800018ba`, size 32, and `cpus` at table 18, row 219,
value `0x800123e8`, size 1024, retaining all other raw symbol fields. The
`executable_elf` certificate checks the actual header type field equals 2.
These facts connect the earlier concrete mycpu addresses to symbol entries;
they are not function-correctness, executable-byte, or fetch proofs themselves.

## Independent validation

- Build `Xv6.Kernel.SymbolImageProofs`: passed 465 jobs.
- Fresh direct Lean elaboration of
  `Xv6/Generated/KernelSymbolCertificates.lean`: passed, independently replaying
  the full 222-index ordinary-kernel certificate.
- `python3 tools/symbol_certificates.py .upstream/xv6iris --check`: passed.
- `lake env lean tests/KernelSymbols.lean`: passed without warnings. Its 15
  kernel-checked fixtures cover valid/suffix/empty names, bounded termination,
  row/link/type/entry-size/payload/magic failures, both compression guards,
  absent packed data, and the documented selected-reader/global-validator
  distinction. Fixture construction is independent of the production parser.
- Fresh audit of all 109 physical-origin logical declarations across the five
  modules: passed. Traversal includes types, opaque bodies with
  `allowOpaque := true`, and inductive constructors. Only `propext`,
  `Classical.choice`, and `Quot.sound` are permitted; no unsafe/partial semantic
  dependency occurs. The sole excluded root is the compiler-generated
  `Xv6.Elf.readCString._unsafe_rec` companion of the safe, structurally recursive
  `readCString`. The logical proof cones do not reference it.

Audit driver and logs are under `/tmp/xv6-lean-research/`:
`KernelSymbolParserPeerAudit.lean`, `kernel-symbol-parser-peer-audit.log`,
`kernel-symbol-parser-peer-build.log`, `kernel-symbol-parser-peer-checks.log`,
and `kernel-symbol-certificates-peer-replay.log`.

Reviewed SHA-256 values:

```text
024feb2641526bd7463631b36c42468f5dc732ce8747e086e01b0f1f5634705c  Xv6/Elf/SymbolDefs.lean
a4880e09a2914df33c56f19997a174b96c60530af8561bd61c4a656f6b816d6e  Xv6/Kernel/SymbolDefs.lean
ed8f1f3111190854702e3c92b780789e8c70aca5db70180e79c8088bad043191  Xv6/Kernel/SymbolProofs.lean
7f88194e2efe0c15882bbb4f87342304bb635ca456de4f0bb052596dc768ec6f  Xv6/Generated/KernelSymbolCertificates.lean
9f8249bc2510d10adff4f6a73654c7a3e9bd7c0d31e1157e1bf674891c84c216  Xv6/Kernel/SymbolImageProofs.lean
4bb2e8a08cdea8041f97a8e4c39188806fd58f0cc64194b852c56bfa309eb6f6  tools/symbol_certificates.py
```

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
