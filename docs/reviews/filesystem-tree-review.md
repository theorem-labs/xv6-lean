# Independent review: filesystem tree and actual paths

Reviewer: Codex coordinator. Read Tree/TreeDisk definitions, specifications,
proofs and actual-image leaf. Compared FsTree.v100–163,605–847 and the
FsImg.v464–545 node/store construction directly.

The carrier records arbitrary file byte lists and directory maps. NodeRep
requires live non-directory type for files and uniqueness for directory
representations. nodeOf itself remains total, preserving malformed device
payload bytes. Dotdot is an ordinary entry. Acyclicity, proper paths, inode
bounds and root-directory shape are separate propositions.

Path traversal uses the source option fold; an empty path returns its starting
inode even when missing. The finite store inserts precisely the bounded live
records. Lookup proofs cover negative and out-of-range indices and avoid
reducing the complete store. Full fsimgValid supplies the exact TreeWellFormed
predicate and representations of all present nodes, without claiming acyclicity.

Concrete echo/init/sh/sync and dot/dotdot paths use the complete certified
root-directory bytes and first-match lookup; no host path lookup is trusted.
Review: PASS for this pure representation layer. File contents against
independently imported user ELFs, path parsing and native tree ownership remain
separate later work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
