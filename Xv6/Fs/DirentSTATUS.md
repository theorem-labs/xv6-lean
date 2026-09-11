# Directory byte and first-match foundation

`DirentDefs` and `DirentProofs` port the pure foundations required by the
remaining initial filesystem checks. Sources at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476` are `DirentEnc.v` (record,
canonical names), `InodeDefs.v:8–9` (file bytes), `DirView.v:56–338`
(ascending first scan and record views), `DirView.v:757,824,963`
(count/inum/dot predicates), and `FsTree.v:101–451` (names and first-winner map).

Raw names are `List (BitVec 8)`, with arbitrary source length; a record's
14-byte shape is a separate predicate. Canonical names stop at the first
NUL and are capped at 14 bytes. File bytes retain the exact 1024-byte block
index/modulo arithmetic and zero default for missing list positions.
The inum decoder uses the shared byte assembler and its encoder roundtrip
is proved. The name-field reader is tied to the same encoded record.

`dFirst` preserves the source recursion and evaluation order: search the
earlier prefix, return its hit if present, otherwise inspect the next index.
Its Some/None characterizations prove least-match behavior and all-prefix
failure, with monotonicity and extensionality. Record liveness and matching
have Boolean/Prop equivalences.

`NameMap` and `NameSet` use native finite extensional trees over the full
byte-list key carrier. `dirView` retains the source's first-winner filter,
ordered filterMap and first-priority list-to-map fold. The central
`dirView_lookup` proves equality with the inum of `dirFirst` for every raw
byte state, without uniqueness or well-formedness assumptions. Generic
fold/append lookup laws establish the list-to-map correspondence. Under
`DirNamesUnique`, the any-live-record value theorem is additionally proved.

The exact source dot-index predicate retains its directory-type and nonzero
link-count implication guards. No source directory validity clause is
silently strengthened to require these guards unconditionally.

Validation:

```sh
python3 tools/lake.py build Xv6.Fs.DirentProofs
```

All 38 handwritten laws compile (10 jobs, proof module about 0.9 seconds).
The enforced transitive audit covers 189 filesystem foundation theorem
cones and permits only `propext`, `Classical.choice` and `Quot.sound`.
Kernel regressions check NUL canonicalization, full 14-byte names, first
matching duplicate, free-name garbage, duplicate non-uniqueness and the
record-64 block boundary. No native evaluator, `bv_decide`, `sorry` or
custom axiom is used. No concrete image is imported.

Next layers: exact W6/W7/W8 directory/root/dot checks, W9 ticket counts and
the complete `fsimg_wf` Boolean. Path/tree stores, directory mutation rules,
the remaining name/encoder lemmas and durable filesystem predicates remain
subsequent ports; this foundation does not claim those results.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
