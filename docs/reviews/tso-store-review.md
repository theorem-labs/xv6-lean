# TSO ledger store independent review

Reviewed the four frozen `MachCSL/Logic/TsoStore{Defs,Spec,Proofs,Link}.lean`
modules and status against pinned `TsoCtx.v:2622–2665,3459–3510,3951–4064,
4095–4180`, plus the called `TsoAppend` payload-frame proofs and full native
heap representation. Source pin:
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
Result: pass for the stated ownership-update scope; no correction required.

`ledgerByte` is the full-fraction specialization of source `phys_ledger`:
physical byte ownership, its RAM-address condition, and an existential full
timestamp carrying `payNone`. Moving the existential across the separating
conjunction does not change the assertion. `storedByte` retains the exact
exposed new timestamp, and the forgetful lemma removes only that exposure.
Finite-map and offset-list products preserve the source multiplicities.

I checked the bulk native update against `ledger_store_bytes`. Existing full
byte fragments establish the old submap; equal old/new domains establish
that every written address already exists and is RAM. Existing timestamp
witnesses are collected into a finite map without allocating client tokens.
Both full native ghost maps are updated at the existing names. The old
metadata indirection authority and its domain condition are reassembled,
while metadata values and tokens are framed. In particular, this does not
replace the heap with a new allocation or persist writable cells. The proved
`union_eq_std` correctly reverses the operands between Iris's left-biased
union and Std's right-biased union, so replacement values win.

The `Transition` premises exactly state unchanged image, one authored
message append, physical overlay, monotone CPU views, and their new length
bound. The interpretation update advances log ownership, log length, and
all-Nat-agent view ownership, returning the persistent message at the old
length and the new byte timestamps at old length plus one. I inspected the
called append proofs: untouched addresses retain latest-value, pin, window,
release, and word-pin obligations and their original payloads. There is no
untouched-payload simplification or assumed ghost-state preservation.

`windowMap_decode` follows the exact right fold and first-winner behavior
for arbitrary repeated modular addresses. The ownership regrouping requires
`n ≤ 2^64`, matching source `phys_ledger_win_map`; subtracting the base in
64-bit arithmetic proves injectivity of offsets below the modulus without
requiring the address interval itself to avoid wraparound. The generic word
bit width remains arbitrary, as in the source window rule. The stronger
window result exposes the append receipt and timestamp; the source-shaped
`update_window_ledger` correctly discards that extra information.

`Contracts` lists the actual view, history, and monotone-length dependencies.
`nativeContracts` supplies all of them from native Iris proofs, and
`registryStoreSpec` links to the existing FsLink registry. Capacity identity
lemmas establish the same full machine heap and TSO resources; no slot is
added. The theorem intentionally leaves unrelated machine-state fields
unconstrained because it proves the heap/TSO slice, not the complete era or
an operational step.

Independent validation:

- `python3 tools/lake.py build MachCSL.Logic.TsoStoreLink`: passed 387 jobs.
- `python3 tools/lake.py env lean /tmp/xv6-lean-research/TsoStoreIndependentAudit.lean`:
  enumerated all 120 physically originating declarations, including private
  helpers, and traversed every statement/proof dependency. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur; there are no unsafe or partial
  semantic dependencies and no runtime-companion exclusions.

This review does not certify store event WPs, blocked-write behavior,
reservation preservation, full era/power updates, conditional stores, or
mutual exclusion. Those are explicitly outside this component's contract.
The reviewing agent previously contributed some underlying native ghost
libraries; this is an independent review of the root-authored store layer,
not an independent implementation of its entire dependency stack.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
