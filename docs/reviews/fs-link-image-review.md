# Initial filesystem link-family validity review

Root independently read LinkDirectoryProofs, LinkImageProofs and the concrete
LinkImage leaf, comparing their contracts and central reductions against
FsDurImg.v sections 9e–h. The review passes.

The generic directory proof uses the actual first-winning-record view. Only a
winning, nonexcluded, token-bearing record must produce its destination ticket
and matching type. Losing records, the excluded name, and exempt entries are
handled by native inclusion into the larger ticket supply. No directory-name
uniqueness premise is introduced. The concrete ticket specialization uses the
source's executable nondot-self exemption, including its signed inode carrier.

The image proof separately accounts for the root's dot reference and spare root
reference as two tickets. Ordinary tickets are bounded by the complete image's
counts and actual inode multiplicities. Every nonroot node's directory map is
empty under the source initial-image checker, including free nodes in the full
rounded region. The result is native camera validity of the complete family
combined with the extra root fragment, not just per-node entry well-formedness.

The exported image theorem retains all five source premises. The root-no-self
premise is redundant in this inclusion argument because of the exact executable
exemption, and remains explicit. Exact existing node/image reader equality
replaces the source's intermediate bounded-reader transport lemmas without
changing the final map or adding a premise. The concrete leaf applies the
already checked BootImageWF theorem to the full 208-node image; its local
irreducibility hints affect elaboration only.

Independent validation passed 467 build jobs and a fresh physical-origin audit
of all 41 logical declarations and complete type/body dependency cones. Only
propext, Classical.choice and Quot.sound occur; no unsafe/partial dependency or
runtime companion exclusion. Records: LinkImageRootAudit.lean,
link-image-root-build.log and link-image-root-audit.log under
`/tmp/xv6-lean-research/`.

The complete durable snapshot still requires its byte, coverage, bitmap and
cross-node ownership/disjointness clauses and subsequent native allocation.
This result does not assert the full snapshot or kernel correctness.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
