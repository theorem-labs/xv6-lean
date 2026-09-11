# Independent root review: snapshot and home-map contract

Verdict: PASS. Independently read all four Snapshot/SnapshotHome modules,
FsDurSnap.v:261–406,516–546,577–615 and LogDefs.v's home/restriction definitions.
All 21 byte clauses match the source, including arbitrary choice and spare root
link validity, rounded inode-region coverage, signed free-block interval,
cross-node disjointness, full representation and byte ties. The state carrier
contains no hidden validity assumption. Shape has the source's actual single
field; the older source prose is not substituted for the definition.

The home set is exactly coverage minus header plus 30 log slots. The interval
lemma works for arbitrary signed starts. Finite-map lookup and enumeration
independence justify its representation; missing keys read the empty list.
Block-zero exclusion appears only under explicit CovIn. Direct zero and negative
coverage lemmas confirm no implicit positivity filter was added.

A fresh physical-origin audit of all 153 declarations and their complete
statement/proof dependencies passed: standard three axioms only, no unsafe or
partial semantic dependencies, zero exclusions. Independent peer review also
rebuilds the four modules. Command: tools/lake.py env lean
/tmp/xv6-lean-research/SnapshotRootAudit.lean.

These modules state the exact full contract and prove projections/home-map laws.
They do not yet prove Bytes or OK of the initial disk, allocate filesystem
resources, or establish crash consistency.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
