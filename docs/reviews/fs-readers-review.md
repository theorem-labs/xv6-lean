# Independent filesystem byte/record review

Reviewed `Xv6/Fs/{Bytes,Superblock,Dinode,Image,DinodeProofs,DinodeBlockProofs}.lean`
against `FsImg.v` sections 0–3/W1/W2, `DinodeEnc.v`, `BlockWords.v`, and
`FsCrash.fs_blocks`, all at paper pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. No correction required for this
bounded scope.

The disk and block indices remain signed integers. Total byte lookup uses the
source's zero default, so malformed short blocks are read exactly as specified;
the superblock parser independently rejects blocks shorter than 32 bytes.
Little-endian decoding reuses the existing checked assembler. Arbitrary
superblock records retain signed fields and all ten W1 conditions, including
mkfs's `ninodes / 16 + 1` formula rather than ceiling division, one bitmap
block, a nonempty data region and the ushort region bound. The clean-log
predicate takes at most four bytes, as in the source; deriving individual
zero bytes requires the same explicit length bound as the source lemma.

The dinode record keeps the arbitrary address list and a separate length-13
well-formedness condition. Field widths/offsets match the source: four 16-bit
fields at 0/2/4/6, 32-bit size at 8, and thirteen 32-bit addresses at 12.
The decoder uses the source's unsigned-32-bit cast of signed inode numbers,
then block division and slot remainder; it drops the prefix without silently
truncating or padding the block first. Missing indirect blocks yield 256 zero
entries; holes yield 1024 zero bytes; out-of-range list lookups preserve the
source total-default convention. No finite index restriction was added.

`decodeDinode_encode` and byte-encoding injectivity hold under the exact
record well-formedness premise. The final `dinode_of_block` theorem matches
`fs_dinode_of_diblk`: a 16-record well-formed encoded block at the selected
block address decodes to the record at the selected slot. Its two hypotheses
are precisely source block well-formedness and block equality, with no extra
inode-number range or distinct-address requirement. The total default on the
conclusion is unreachable because the checked slot lies below 16.

The concrete superblock and clean-log facts use the actual packed initial
disk. The negative witness changes byte 1024 of that same disk to zero;
`bad_magic_parse` obtains magic `0x10203000` and `bad_magic_rejected` proves
that parsing followed by the actual W1 predicate rejects it. This does not
assume a conveniently invalid abstract record. Reboot retention of live disk
state is not changed by these files.

Independent validation loaded the owner's green compiled modules and audited
all 204 declarations in namespace `Xv6.Fs` with transitive `collectAxioms`.
Only `propext`, `Classical.choice`, and `Quot.sound` were permitted; the key
actual-image parsing/rejection and block-inversion proofs use only `propext`
and `Quot.sound`. The exported block-inversion type was inspected explicitly.
Files: `/tmp/xv6-lean-research/FsIndependentAudit.lean` and
`/tmp/xv6-lean-research/fs-independent-audit.log`.

W3–W8, full filesystem well-formedness/recovery, ghost interpretation, kernel
instruction proofs, and checked cross-prover correspondence remain separate
obligations. This review does not upgrade the partial image facts into a full
filesystem or crash-consistency theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
