# Native filesystem link-supply review

Root independently read LinkSupplyDefs and LinkSupplyProofs and the pinned
FsDurImg.v sections 9a–c, including the full-family reduction with arbitrary
slack. The implementation retains the exact multiset/Auth/map carrier. The
unconditional fullMap validity follows pointwise from full authority plus its
identical fragment; no node validity or directory count premise is hidden there.

The split and single-entry-node reduction are proved using native finite-map
big operations. The arbitrary slack argument is retained, so the later root
keep-alive token can be included in the same allocation. Inclusion is downward
validity of that concrete full map, not an assumed image-validity predicate.

Ticket lists retain multiplicity and are routed using the destination's own
type value. Zero occurrences produce no outer-map key; a zero-multiplicity supply
for a present inode instead retains a present empty fragment. Both distinctions
are proved, as are duplicate-ticket and absent-key examples. Positive count
inclusion requires a real destination inode with sufficient multiplicity.
No mismatch found in the declared source slice.

Independent validation passed 242 build jobs and a fresh physical-origin audit
of all 46 logical declarations and their complete type/body dependency cones,
with only propext, Classical.choice and Quot.sound, no unsafe/partial dependency,
and no companion exclusions. Records: link-supply-root-build.log,
LinkSupplyRootAudit.lean and link-supply-root-audit.log in
`/tmp/xv6-lean-research/`.

The directory-view-to-ticket bridge and actual image-family validity with the
root's spare fragment remain separate obligations, not premises disguised as
proved results of this layer.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
