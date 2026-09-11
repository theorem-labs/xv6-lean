# Independent root review: native RAM writes

Verdict: PASS. Codex root read all five MemoryWriteWP modules and the source
HartEvents.v generic/conditional leaves and wrappers. The direct-node interface
retains the complete dependent present-payload request. Generic writes have no
width or access-kind restriction; conditional readback uses the source strict
n<2^64 bound, and finite ledger conversion uses n≤2^64.

The actual blocked step preserves the cursor, whole state, own reservation and
unopened callback. Success appends exactly one authored snapshot, performs the
actual writeBytes overlay, clears only the writer's reservation and sets its
view according to the real access-kind classifier. Other reservations retain
submap validity because the actual conflict guard protects their footprints.
Absent-payload runtime behavior is distinct from a forged absent event; no
fake success branch was introduced.

Native lifting pays every live successor and stale-generation case, restoring
all seven era components, fixed-world/durable-disk resources and silent trace.
The conditional old word comes from held-snapshot validity, not a caller's
unproved memory equation. The generic pure guard is instantiated by True or
that proved readback. The ledger adapter extracts actual full old bytes and
timestamps and internally invokes TsoStore for the exact successor; it restores
all metadata and returns the actual message and view receipts. Link discharges
all Store/Views/Reservation/Exclusive contracts, with no new camera or oracle.

Fresh component build: 454 jobs passed. A separate physical-origin audit covers
all 58 declarations and complete statement/proof dependencies: standard three
axioms only, no unsafe/partial semantic dependencies, zero exclusions. Records:
/tmp/xv6-lean-research/MemoryWriteWPRootAudit.lean and memory-write-root-audit.log.
These are event WPs and resource adapters; generated store/AMO instruction plans,
lock resource-transfer proofs and operational exclusion remain separate work.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
