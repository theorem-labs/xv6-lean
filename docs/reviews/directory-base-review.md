# Independent review: W6–W8 directory checks

Reviewer: Codex coordinator. Read all Directory modules and source
`FsImg.v:1919–2274`, including the exact `fs_dir_ok` record.

The ascending collector retains only live canonical names, rejects duplicates
and leaves free-entry name garbage unconstrained. The membership and success
theorems prove exactly the original name-uniqueness predicate. W6 retains all
five source clauses: record granularity, live in-range targets, unique names,
the actual finite-map dot lookup and existence of a dotdot lookup.

The root check requires a directory and dotdot targeting inode1. W8 separately
pins the two live dot records to slots0 and1. Its implication-shaped exported
predicate retains the source type/link-count guards, while the Boolean sweep
checks every directory exactly as the source does. Negative inode counts retain
the source's empty-sweep behavior; W1 supplies the valid-size constraints later.

Kernel examples demonstrate why W8 cannot be inferred from W6 and W7: swapped
dot records satisfy both lookup-based checks but fail the index check. Other
examples reject dead targets and duplicate live names while accepting name
garbage in free entries. Review: PASS for the pure checks and projections.
Actual image certificates, W9 and tree-level projections remain separate work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
