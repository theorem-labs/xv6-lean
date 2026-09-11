# Independent generic encoding-certificate review

PASS. Read the complete `Xv6/Image/EncodingProofs.lean` and its strict decoder,
packed byte access, packed coverage, and source byte-assembly dependencies.

The certificate includes decoded byte length as well as the assembled integer,
so leading/trailing zero bytes cannot disappear. Appending a block requires a
successful strict decode, preserves the exact string/list append order, and
shifts the right payload by precisely eight times the left byte length. The
per-page induction requires every nonfinal page to be 4096 bytes; the final page
may be short or empty. The empty final page causes no missing-data default:
`Packed.getByte?` retains the explicit global byte bound. The whole-image theorem
relates exact decoded bytes to packed lookup at every offset, including absent
out-of-bounds offsets. No circular assumption of packed/hex equality occurs.

Kernel regression checks reject invalid hexadecimal `0g` and odd-length `00f`,
check zero-preserving little-endian `0001` = two bytes/value256, and check all
lookups in a zero-length one-page image are absent. A direct fresh import audited
all68 image theorem cones, including private module helpers; only propext,
Classical.choice and Quot.sound occur. No build of generated proof shards was
started by this review.

Scope: this approves the generic certificate calculus. Actual KernelElf/FsImg
certificate-root generation and complete shard verification remain separate
concrete build gates, owned by the root and logic agent.

Replay:
`PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/EncodingIndependentReview.lean`

Reviewed SHA256: 3fd6420adc11a93a46a239352680529952ba3fe9faa141f7cc992e972792425f

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
