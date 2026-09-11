# Native durable byte flattening and ledger cut

Frozen bridge for `FsDurBytes.v` and the byte-map identity in
`FsDurRead.v`, at xv6iris `arxiv-v1`
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The five modules retain signed, unbounded `Int` byte and block keys,
left-biased union, and the existing finite block and byte map carriers.
`byteRun` is native `map_seqZ`; its lookup and cardinality laws preserve
all list bytes without wrapping. `flattenList` is the source right fold
of left-biased block byte maps. `flatten` supplies the Lean finite map's
enumeration. `DbytesOK` is exactly the source at-most-1024-byte condition;
`BlocksFull` is the separate exactly-1024-byte condition.

Under `DbytesOK`, lookup, fresh insertion, block separation, and arbitrary
permutation of the map enumeration are proved. This establishes the
source-compatible flattening independently of finite-map enumeration
order on guarded inputs. No equality with Rocq's concrete enumeration
order is claimed for malformed overlapping oversized blocks. The
kernel-checked `malformed_order_matters` counterexample demonstrates that
this qualification is necessary. A separate negative-address example
checks signed addressing. Later snapshot consumers must discharge this
guard from their existing full-block clause; it is not a global premise
silently imposed on arbitrary maps.

`byteRun_ledger` and `flatten_blocks` prove native Iris resource
equivalences for any filesystem view, using full byte ownership and the
exact source block-length condition. No exclusivity assumption is added.
`provided_image_cut` splits a provided image ledger into the requested
submap and its exact difference, retaining an arbitrary frame.
`provided_image_cut_with_auth` also retains the exact original disk
map authority. Neither rule allocates or updates an authority.
The concrete link uses the same disk image camera at slot 12 in the
actual registry extended through the lock and top-inode cameras.
`snapAuth` retains the source existential byte map and its subset
orientation: the authorized map is a submap of the flattened blocks.

Validation: `python3 tools/lake.py build MachCSL.Logic.FsDurBytesLink`
passes **406 jobs**. There are **32 named theorems**. A fresh
physical-origin audit checks all **77 declarations** across the five
modules, including private/generated declarations and their transitive
types, bodies, and referenced constructor fields. Only `propext`,
`Classical.choice`, and `Quot.sound` occur, with no unsafe or partial
semantic dependency and zero exclusions. The audit source is retained at
`/tmp/xv6-lean-research/FsDurBytesOwnerAudit.lean` in the working environment.
No `sorry`, custom axiom, `native_decide`, or `bv_decide` is used.
The parent reviewed the frozen definitions and specification contracts;
full proof review is pending.

This checkpoint does not yet name all filesystem footprint slots, prove
their pairwise separation, regroup their ledger into `fs_state`, or
allocate the complete native `P_dur`. Those are the next source
`FsDurAlloc.v` dependencies. The arbitrary malformed fold-order
correspondence remains explicit above rather than being replaced by an
unchecked host assertion. Existing frozen modules and umbrellas were
not changed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
