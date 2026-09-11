# Independent TSO history review

PASS. Reviewed all four modules against pinned `iris/TsoGhost.v` sections2
(dset resource laws) and5 (dirty_ok), plus native Iris ghost-map and set-camera
interfaces. Direct independent replay of `/tmp/xv6-lean-research/TsoHistoryAudit.lean`
audited148 declarations with only propext, Classical.choice, Quot.sound.

The dirty set uses the ordinary union camera, not the disjoint-union camera.
Persistent singleton receipts can be minted repeatedly; inserting an already
present key needs no freshness premise. Fractional agreement and member lookup
are derived from actual native auth validity, and updates preserve arbitrary
frames. The exact dirty_ok author branch keeps timestamp=i+1 and author equality
without adding an address-equality premise absent from the source.

The log map stores actual Message64 records under zero-based indices. LogRep
quantifies every index, so its append theorem establishes both the next fresh
position and absence of extra entries beyond the represented list. Appends mint
discarded persistent receipts and preserve an arbitrary Iris frame. The
visibility consequence uses the real visible predicate and actual represented
log lookup, with its explicit bound≤view premise.

Slots4/5 extend the previous registry; slots0–3 and all≥6 are proved unchanged.
The mono-nat capacity remains slot3 and is reused rather than duplicated. Link
constructs each client specification from actual implementations and explicit
capacities, without assuming initialized machine state. Full state
interpretation, metadata and adequacy remain outside this resource slice.

No production edits requested.

SHA256:
MachCSL/Logic/TsoHistoryDefs.lean c8f75b7c8ca28e5a90376903c43f081ad0644a0fb182732ea0fd3216b8bec86c
MachCSL/Logic/TsoHistorySpec.lean 8a9e982960f4e74ba38d0d1643387bedf6d5391a9e449c07736592f521554a3e
MachCSL/Logic/TsoHistoryProofs.lean 73e743750031e5def7e19e0c38ee9b6e1c05ecff29deff5138e0dee4b175933d
MachCSL/Logic/TsoHistoryLink.lean 92b22d745bbd65a52478f95876feb97467acb1db1c36105e830733292cc31793

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
