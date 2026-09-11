# Independent review: durable inode and link image predicates

Reviewer: Codex coordinator. Read DurableInode and DurableLinks definitions,
proofs and actual image leaves; compared directly with FsImg.v2466–2568 and
3337–3440 at the paper pin.

The durable inode checker preserves all five source Boolean groups and eight
record fields. It admits committed zero-link orphans and valid allocations
beyond size, requires coverage below size, and rejects metadata addresses.
Both Boolean/record directions and W3 implication are proved. Size movement
retains type/addresses and explicitly requires coverage at the new size.
The actual complete inode sweep follows the checked W3 sweep.

The separate exact-link sweep skips free and directory records. Root no-self
preserves the source's nested branch structure and restricts self-targeting
live names to dot and dotdot. Both actual-image checks use the already certified
ordered tickets and complete root data. Neither is incorrectly claimed as a
consequence of W9 alone. These are components of durable initialization,
not a proof of transaction or crash consistency.

Review: PASS for these components and their bounded projections. Entry-derived
used sets, tree/path structure and durable Iris resources remain open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
