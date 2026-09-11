# Independent bitmap base review

Result: no correction required for the declared pure base. Reviewed the
frozen `Xv6/Fs/BitmapDefs.lean`, `BitmapSpec.lean`, `BitmapProofs.lean` and
`BitmapSTATUS.md` against `iris/FsImg.v` §§5/9 and the W4/W5 checker arm at
paper pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The independently
changing concrete `BitmapImage` leaf is outside this review.

`collectNodup` preserves the source tail-first traversal and rejects a
repeated element. Its successful set contains exactly the list's members;
success is equivalent to list `Nodup`, and failure is equivalent to its
negation. It specializes the source polymorphic `gset_nodup` (776–809) to
signed block numbers; a future use for other element types needs its own
extension. It does not turn duplicate rejection into duplicate removal.

`inodeBlocks`, `usedBlocks` and `usedSet` match 1309–1361. An indirect block,
when present by the size condition, precedes direct and then indirect
content blocks. Unchecked records retain total zero-default list lookups,
unsigned stored fields, signed intermediate arithmetic and `toNat`
truncation. Free records are skipped exactly when their type is zero.
The live-subset/input equalities do not replace the original readers with
untrusted input assumptions. The per-inode membership/Nodup and W3 range
projections match the source's corresponding arguments (1578–1591,
1630–1660).

`bitmapBit` matches source `fs_bit` (1739): Euclidean division/modulo precede
the natural byte/bit-index conversion. Since the remainder lies in `[0,8)`,
the byte's `getLsbD` has the source nonnegative `Z.testbit` meaning. Short
lists return the zero byte. The regression at bit -1 correctly observes
bit 7 of byte 0; it deliberately does not reject a negative bit address.

`bitmapValid_iff` and its projections preserve the exact W5 meaning
(1763–1799): every metadata or used block below `size` is set and every
other checked block is clear. No tail-bit condition is added. This includes
metadata block 0 when the bounds imply it and empty checks for nonpositive
sizes. `bitmapSet` preserves every set bit within its separately stated
byte bound (1824–1836), including bitmap padding beyond filesystem size.
`bitmapSet_free` generalizes the source's `fs_bmap_set_free` (1887–1902) to
an arbitrary byte count with precisely the needed one-bitmap bound; source
`SuperblockOK.oneBitmap` specializes it at 1024 bytes.

`blocksBitmapValid_iff` proves exactly the W4/W5 arm of `fsimg_wf`
(3446–3450). It is not a theorem for the entire filesystem image checker.
The status correctly defers source slot-index bijection/injectivity,
cross-inode disjointness needed to carve ownership, and the `BitmapEnc`
encoder/reader roundtrip. No such omitted fact is silently assumed by the
34 exported base theorems.

Independent validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Fs.BitmapProofs
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/BitmapIndependentAudit.lean
```

The 13-job build passes. The separate audit replays all 266 imported
filesystem/bitmap theorem cones and accepts only `propext`,
`Classical.choice` and `Quot.sound`. Its output is
`/tmp/xv6-lean-research/bitmap-independent-axioms.log`. The existing ordinary
kernel regressions cover duplicate rejection, negative indices, metadata
bit zero, unconstrained padding and negative-size vacuity. No production
file was changed by this review.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
