# Used blocks and bitmap: W4/W5 base

`BitmapDefs`, `BitmapSpec` and `BitmapProofs` port the pure collection and
bitmap layer of `iris/FsImg.v` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

| Source | Lean |
| --- | --- |
| `gset_nodup` and projections, 776–809 | `collectNodup`, membership, Nodup and exact failure laws |
| `fs_inode_blocks/used_blocks/used_set`, 1309–1361 | `inodeBlocks`, `usedBlocks`, `usedSet` |
| per-inode NoDup and list range, 1578–1591, 1630–1660 | `usedBlocks_nodup_inode`, `inodeBlocks_range`, `usedBlocks_range` |
| `fs_bit`, `fs_bitmap_wf/spec/free`, 1739–1799 | `bitmapBit`, `bitmapValid`, `BitmapOK` and iff/free projections |
| `fs_bmap_set/elem/free`, 1824–1836, 1887–1902 | `bitmapSet`, membership and free-block projections |
| W4/W5 image-check arm, 3446–3450 | `blocksBitmapValid`, `BlocksBitmapOK`, exact iff |

The finite extensional `BlockSet` is `Std.ExtTreeSet Int`. Collection walks
the tail before testing the head, returning `none` at a duplicate exactly as
the source does. The successful result has exactly the input membership;
success is equivalent to `List.Nodup`, and failure to its negation. The proof
does not replace rejection with duplicate removal.

Each inode contributes its indirect block first when its size needs one,
then its direct content and indirect content blocks. All signed arithmetic,
source `toNat` truncations, arbitrary address-list lengths and total default
reads are retained. Free records are skipped only by their zero type. The
live-subset rewrite and input factoring are generic checked equalities for
reusing already certified record/indirect inputs. Per-inode membership and
Nodup follow from the complete collection, and W3 implies every listed block
is in the data region.

`bitmapBit` uses Euclidean division/modulo before the source natural index
conversion. It agrees definitionally with the byte's natural `testBit`;
the remainder is proved in [0,8). For example bit -1 reads bit7 of byte0,
as in the source. Short byte lists default to zero. W5 checks exactly
0 through `size-1`: every metadata block, including block0 when applicable,
and every used block is set; other checked blocks are clear. Negative sizes
produce empty checks. Bitmap bits at or beyond `size` are unconstrained.
`bitmapSet` retains all set bits below its own explicit byte-size bound,
including such padding bits; its free-block theorem separately requires
the filesystem's size to fit that bound.

The core contains no concrete image imports. Validation:

```sh
python3 tools/lake.py build Xv6.Fs.BitmapProofs
```

The 13-job build passes in about one second for the proof module; all 266
imported filesystem theorem cones are audited, allowing only `propext`,
`Classical.choice` and `Quot.sound`. Kernel regressions reject duplicates
and clear metadata bit0, accept unconstrained padding, preserve negative
bit-index behavior and negative-size vacuity. No native evaluator,
`bv_decide`, `sorry` or custom axiom is used.

Outstanding separate bridges: the 269-slot index bijection/injectivity,
cross-inode block-set disjointness for carving, and the `BitmapEnc` byte
encoder/reader roundtrip. These source results are not claimed by this
bounded base. Concrete W4/W5 image certificates belong in the separate
`BitmapImage` leaf; they are not premises of any generic proof.

The concrete leaf is now complete. `used_blocks_input_eq` composes all 22
previous W3 record and indirect-entry equalities with the exact live-inode
enumeration. `used_inputs_literal` checks the resulting ordered list against
an untrusted 936-block cache. A kernel-checked permutation to the interval
47–982 proves both its membership and duplicate freedom; the proved
collector-success equivalence then supplies the exact `usedSet` result.
No executable sorting algorithm or native evaluator is trusted.

`initial_bitmap_bytes`, in `BitmapData.lean`, checks the full actual 1024-byte bitmap
block against its untrusted literal cache. `initial_bitmap_bit` certifies
every one of the 2000 source-checked bit positions. These two independent
paths meet at `bitmap_valid_checked` and the complete original Boolean
`blocks_bitmap_valid_checked`; `blocks_bitmap_ok` exports its Prop projection.
The actual image has 936 distinct used inode blocks, exactly 47–982, and its
bitmap marks blocks 0–982. Generic proofs continue to allow arbitrary padding.

`tools/bitmap_certificates.py` checks the source lock, checkout revision,
working source equality with the pinned Git blob, and the same complete raw
image hash/size as the W3 producer. Its output preserves order and repeated
blocks rather than deduplicating them. Generated headers retain source pins,
hashes and kernel license attribution. Every literal has an independent Lean
equality to the original reader or already reader-certified W3 inputs.

```sh
python3 tools/bitmap_certificates.py .upstream/xv6iris --check --self-test
python3 tools/lake.py build Xv6.Fs.BitmapImage
```

The complete image leaf built in 4.85 seconds with peak RSS 2,162,448 KB,
after the separate bitmap-data leaf (6.76 seconds / 2,153,148 KB). Abstract
assembly lemmas in `BitmapCertificateProofs` keep image readers opaque while
joining certificates. The final image module enforces a transitive axiom
allowlist over all imported filesystem, W3 and bitmap theorem cones.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
