# Full initial filesystem checker

`ValidityDefs.fsimgValid` is the exact eight-conjunct FsImg.v3442–3453 `fsimg_wf`
(W1 throughW9; W4/W5 share the failure-aware block/set branch). `ValiditySpec`
exposes those same Boolean premises and `ValidityProofs` proves their equivalence,
source superblock/log/inode/used/dir/root/dots projections, and all-integer link
bounds, directory exclusion, and root link facts.

`ValidityImage.fsimg_valid_checked` proves the complete checker for the actual
pinned disk's `blockView` and parsed superblock. It composes already checked reader
certificates. Initial build271jobs; full leaf1.1seconds; enforced682 theorem cones
standard foundational axioms only. No native certificate axioms are accepted.

The source's tree-root and block-slot-injectivity projection theorems depend on
further vocabulary and generic bridges, still to be ported; they are consequences,
not omitted premises of this checker. Durable DWF, `fs_links_eq`, and
`fs_root_no_self` are separate source predicates and follow next. Initial image
well-formedness alone is not machine adequacy or crash consistency.

Authorship note: researched and written by OpenAI Codex on Jason Gross's behalf.
