# Context byte-window store and native write: independent review

PASS. Reviewer: `/root/lean_logic_audit` (OpenAI Codex), independently of
the coordinator who authored both families. Read every definition,
specification, proof and native Link in the eight TsoContextBytesStore
and TsoContextBytesWriteWP modules. Compared against the existing native
TsoContextStore/TsoStore/MemoryWriteWP implementations, actual Node write
semantics, TsoCtx.v:2572–2587 and HartEvents.v:797–839 at the pinned source.

The map/window correspondence requires n≤2^64, exactly the modular-key
injection bound: each offset is strictly below 2^64 even when n equals
that bound. The starting address can wrap; alignment and a whole-window
no-wrap premise are unnecessary. Zero width remains allowed. All physical
bytes still require their actual RAM ownership, so the algebraic maximum
width does not assert that a full-address-space RAM resource is inhabitable.
The event index n is distinct from the request's metadata size, and the
complete request is retained without silently equating them.

The finite-map update consumes full old registered context bytes, derives
same-domain replacement internally, retains old dirty entries and registers
every new authored key at one common positive timestamp. It uses one real
log append, retains every ordinary CPU view, preserves full heap metadata
and TSO interpretation, and reconstructs all-view own-author readback.
It imposes no pristine-byte premise or local-load view advancement.

The WP's successful state is exactly MemoryWriteWP.writeState. Its internal
bundle callback separates and restores the unchanged register/device portions
around the real heap update. Resource mutation runs after the actual event's
later under the native mask transition. The existing leaf rule proves every
live successor and dead-generation behavior; blocked retries retain the
same reservation, original context/window and unopened callback. Success
clears only the writing hart's reservation and supplies the unchanged-view
receipt. The public rule supplies no update callback, state correspondence,
reservation-disjointness or successful-response oracle. Its continuation is
the genuine actual `.Ok none` residual WP.

Independent combined target rebuild passed **474 jobs**. Fresh strict
physical-origin audits passed **14 declarations in four store modules** and
**32 declarations in four write-WP modules**, including every type, opaque
body and constructor: standard three axioms only, no unsafe/partial cone,
zero exclusions. All eight source hashes remained unchanged. Evidence:
`/tmp/xv6-lean-research/TsoContextBytesStorePeerAudit.lean`,
`TsoContextBytesWriteWPPeerAudit.lean`,
`tso-context-bytes-store-peer-audit.log`,
`tso-context-bytes-write-wp-peer-audit.log`,
`tso-context-bytes-store-peer-build.log` and
`tso-context-bytes-store-peer.sha256`.

No correction requested. Scope is registered physical context storage and
one ordinary present-payload RAM event. Virtual translation, conditional
PTE writes and four-byte instruction/function composition remain separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
