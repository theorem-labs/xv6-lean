# Initial filesystem W3 certificate

`Xv6.Fs.Image.inodes_valid_checked`, in `InodeW3Certificates.lean`, proves
the exact `inodesValid blockView superblock = true` check for the actual initial
filesystem. `live_inode_ok` projects all nine source W3 obligations for every
member of its actual `liveSet`. The source is `iris/FsImg.v` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; definitions and readers are unchanged.

The pure `InodeW3Proofs.lean` factors only the repeated indirect-entry reader.
`inodeValid_eq_inputValid` is a definitional equality. Its assembly theorem
requires both the actual inode-record equality and the actual indirect-reader
equality before accepting an externally supplied literal check. The separate
`inodesValid_of_live` theorem preserves the source's type-zero skip exactly.
It does not infer any other validity condition for free inode records.

The concrete proof uses the independently proved `live_inode_list` of exactly
1 through 22 to discharge the complete 200-advertised-inode sweep. There are
22 leaf modules; each proves four facts:

- its full literal record equals the actual `dinode` reader;
- its 256 literal indirect entries equal the actual `indirectEntries` reader;
- the exact factored W3 Boolean check holds;
- the original `inodeValid` holds for that actual inode.

Every leaf uses ordinary kernel-checked `decide`. `DiskReaders` supplies proved
normalization of the original block-list readers; signed addresses, uint32
inode-index wrapping and total default reads retain their source definitions.
The Python producer supplies no trusted theorem or assumption.

`tools/inode_certificates.py` verifies the upstream lock, exact checkout commit,
working source equality with its pinned Git blob, and the raw image's
2,048,000-byte size and SHA256
`77f42e2f20c0c2c72234dc9ea034f808a26a003f50e7bba62befe8c174bd07b5`.
Generated provenance additionally records the source Git blob and source-file
SHA256. Kernel software notices point to `LICENSES/xv6-riscv.txt`.

Reproduce and validate:

```sh
python3 tools/inode_certificates.py .upstream/xv6iris --check --self-test
python3 tools/lake.py build Xv6.Fs.InodeW3Certificates
```

The full certificate build passed 247 jobs in 32.97 seconds, with peak RSS
2,084,940 KB in this environment. Its enforced transitive audit checked 326
filesystem and W3 theorem cones, permitting only `propext`, `Classical.choice`
and `Quot.sound`. No native evaluator, `bv_decide`, `sorry` or custom axiom is
used. Producer regressions reject invalid inode fields, truncated input,
wrong source revisions/blobs and modified generated output. The record and
entry equalities remain mandatory regardless of the producer's host checks.

The rounded 208-inode region's free tail, nlink and bare-record checks are
separate theorems in `InodeImage` and `InodeCertificates`; W3 alone does not
establish those conditions. Bitmap ownership, filesystem traversal/namespace
validity, crash invariants and the full paper theorem remain separate work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
