# Generated image encoding certificates

The generator preserves the pinned kernel ELF and fs.img byte sequences and
packed numeric page literals. It changes each imported hex chunk's Lean syntax
to a balanced tree of two-character hexadecimal literals. A matching balanced
proof tree composes 256 reusable, kernel-reflexivity byte certificates through
`hexBlockString_append`. Only whole-page results receive global declarations;
internal tree nodes do not create hundreds of thousands of declarations.

There are 306 distinct pages across both files (305 full 4096-byte pages and
one short 2936-byte page). Repeated pages use the same string definition and proof. In these exact
inputs, the kernel has 70 distinct chunks and the disk has 236 distinct chunks
out of 500; the two files share no complete page. All-zero disk pages are
among the repeated pages. The generator also supports cross-file reuse. The 39 data/proof shards have
at most eight distinct pages each. The kernel image is emitted first, enabling
its certificate closure to build independently before the remaining disk
certificates. In total the importer emits 85 files, including the four existing
raw/packed image modules. The generated certificate/data source is about 52 MiB
before compression; the theorem population is 256 byte lemmas, 306 page lemmas,
and six whole-image encoding/decode/lookup lemmas, not a declaration per byte
or per internal tree node.

The key efficiency property is definitional sharing of the *unevaluated*
balanced string expression: no proof needs to reduce a 4096-byte decoder or
prove a giant literal string equal to evaluated concatenation. Final packed
integer equality uses ordinary Lean reduction of the balanced arithmetic
expression. Generated proof files contain plain `rfl` leaf proofs and explicit
applications of the generic append theorem; no metatactic, native evaluator,
custom axiom, or external implementation establishes a theorem.

Initial measurements:

- Twenty direct 16-byte leaf certificates: 2.73 seconds, about 1.99 GB.
- Twenty direct 8-byte leaf certificates: 1.76 seconds, about 1.78 GB.
- 256 byte leaf certificates and 1000 two-byte compositions: 4.71 seconds,
  about 1.77 GB.
- The first actual 4096-byte kernel page, with its balanced proof and all
  256 leaves: 2.44 seconds, about 1.23 GB, using plain `rfl` leaves.
- Dense eight-page production proof shards: about 64–66 seconds each with
  two concurrent Lean workers. Data shards take about 4–6 seconds each.

These timings are measurements on the current host, not promised CI timings.
The coordinator raised the CI timeout to accommodate cold proof/model builds.

`images.py --check` checks every deterministic generated file, rejects missing
or stale content and unexpected certificate-prefix files, and still checks
both pinned source image sizes and SHA-256 values. The existing packed numeric
files are byte-for-byte unchanged. All five importer tests pass.

The completed and compiled whole-image theorem statements are
`Xv6.Generated.kernelElfEncoding`, `kernelElf_decode_eq`, `kernelElf_lookup_eq`,
and their `fsImg` counterparts. They prove strict hex decoding and all-offset
partial-byte agreement with the packed representations. They do not prove
ELF loading, filesystem well-formedness, instruction safety, or a checked
cross-prover correspondence with the original Rocq terms. The importer remains
an untrusted provenance step; proof checking certifies the Lean representations.

Validation is complete:

- The kernel certificate closure built successfully (31 jobs).
- The disk certificate closure built successfully (75 jobs). After the kernel
  closure and shared data shards were available, the measured disk build took
  981.53 seconds (16.36 minutes), with maximum single-process RSS 1,436,692 KiB.
  This is an incremental measurement, not a complete cold-build timing.
- The combined audit traversed all 874 generated namespace data/proof
  declarations and the six whole-image roots. Their only transitive axioms are
  `propext`, `Classical.choice`, and `Quot.sound`. The audit took 1.49 seconds,
  with maximum single-process RSS 1,661,800 KiB.
- `python3 tools/images.py --check .upstream/xv6iris` reproduced all 85 files;
  `python3 -m unittest tests/test_tools.py` passed all five tests.
- The existing `tests/Images.lean` executable checks, replayed with the minimal
  `Xv6.Images` import, passed: strict decoding, both full image lengths, ELF
  magic, sampled packed bytes in every page, final bytes, and bounds checks.
  These executable checks supplement the complete kernel-checked encoding
  theorems; they are not themselves theorem evidence.

The actual data/proof outputs and generator are frozen for coordinator
integration. Logs and the audit source are in
`/tmp/xv6-lean-research/{disk-encoding-build.log,all-encoding-audit.log,AllEncodingAudit.lean,encoding-runtime-check.log}`.

The preserved image hashes are:

- Kernel ELF: 285560 bytes,
  `b4bd19f162efb9584b841508408035de7e41a4c680311a514e4e78b8f06eedd8`.
- fs.img: 2048000 bytes,
  `77f42e2f20c0c2c72234dc9ea034f808a26a003f50e7bba62befe8c174bd07b5`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
