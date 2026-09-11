# On-disk filesystem port

This directory begins the pure filesystem interpretation from `iris/FsImg.v`,
`DinodeEnc.v`, `BlockWords.v`, and `FsCrash.v` at the pinned paper commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
It does not establish the complete `fsimg_wf` predicate, a durable filesystem
snapshot, recovery correctness, or xv6 crash consistency.

| Source vocabulary | Lean module and result |
| --- | --- |
| `fs_blocks`, `fs_le_at`, byte/word/indirect encoding | `Bytes`: total signed disk/block addressing, exact block length, byte reads, little-endian round trip and indirect word lookup |
| `fs_parse_sb`, `fs_sb_wf`, `fs_sb_ok` | `Superblock`: exact parser and all ten geometry clauses, with boolean/proposition equivalence and metadata/inode-region bounds |
| `fs_log_clean` | `Superblock`: clean-log equivalence and per-byte zero consequence |
| `dinode`, `dinode_bytes`, `diblk_bytes`, `IBLOCK`, `islot` | `Dinode`: unchanged field widths, arbitrary address list, separate record/block well-formedness |
| `fs_dinode`, `fs_ind_ents`, `fs_blk_addr`, `fs_data_of` | `Dinode`: modulo-32 inode indices, zero-default total list reads, exact indirect and hole behavior |
| Encoder/decoder reuse | `DinodeProofs`, `DinodeBlockProofs`: every well-formed record round-trips; decoding a slot of an encoded full block returns that exact record |
| Concrete mkfs superblock and log | `Image`: the pinned disk parses to `(0x10203040,2000,1953,200,31,2,33,46)`, satisfies W1 and has a clean log |
| Rejection witness | `Image.bad_magic_rejected`: changing one actual superblock input byte preserves parsing but fails the geometry check |

The block decoder theorem retains exactly the source's two hypotheses: the
sixteen encoded records are well formed and the selected disk block equals their
encoding. It does not add an inode-number range assumption. Signed superblock
fields remain unrestricted outside `SuperblockOK`; the geometry uses mkfs's
`ninodes / 16 + 1`, not a substituted ceiling formula.

The definitions and pure proofs are separated from the concrete image leaf.
`Image` imports the pinned disk; future caller proofs should consume abstract
filesystem contracts, not re-evaluate literal image contents. The existing source
maps and bitvectors still need their declared cross-prover correspondence.

Validation: all six modules compile with Lean 4.32.2. Independent source review
and a transitive audit of all 204 declarations passed with only the three allowed
standard axioms; see `docs/reviews/fs-readers-review.md`. The concrete parse,
one-byte rejection and block decoder inverse use only `propext` and `Quot.sound`.
The remaining inode validity, bitmap, directory/tree, durable snapshot and recovery
layers are separate outstanding obligations.

`InodeValidityDefs/Proofs` add the exact W3 predicates and separate rounded-region
checks; see `InodeValiditySTATUS.md`. `DiskReaders` proves direct disk-byte forms
equal to the block/list readers. `InodeCertificates` now proves all initial
region link-count and bare-record checks, and combines the link-count check
with tail-freedom as `region_valid_checked`. The full initial W3 certificate
remains separate work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
