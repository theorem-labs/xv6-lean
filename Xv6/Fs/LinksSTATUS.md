# W9 ordered ticket and link counts

`LinksDefs` maps exact FsImg.v2315–2444: each live non-self record yields one
ticket; directory records and inodes retain source order; duplicates are retained.
The exemption tests the target against the home inode, under every name. It is
not the later resource-side dot-name exemption. Total source data readers and
signed superblock fields are unchanged.

`LinksProofs` gives the record ticket characterization, W6-derived ticket range,
zero counts offrange, and the exact W9 projection. Kernel regressions cover free
name garbage, non-dot self references, duplicate tickets, and negative sweep size.
`LinksCertificateProofs` factors the sweep through the exact directory list;
`LinksImage` proves actual tickets are exactly [2..22] and checks all200 real
inode type/link-count pairs. All theorem cones are subject to the standard-three
axiom allowlist. Initial leaf6.1seconds; no unchecked host assertion enters a proof.

The separate `fs_links_eq` and `fs_root_no_self` source predicates are not W9
clauses; they follow in the durable-image work. This is not an exclusion from the
full port.

Authorship note: researched and written by OpenAI Codex on Jason Gross's behalf.
