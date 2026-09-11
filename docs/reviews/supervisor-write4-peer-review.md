# Four-byte supervisor checked write: complete independent review

PASS. Reviewed by `/root/lean_logic_audit` (OpenAI Codex), independently
of the coordinator who authored the five SupervisorWrite4 modules. I read
Defs/Spec/Plan/Proofs/Link completely and compared against the actual
LeanPaperStock Mem.lean:534–625, PhysMemInterface.lean:292–326,
Platform.lean:711–719, and source HartSMem.v:2930–3103. The previously
reviewed native byte-store/write-WP dependencies were also checked at the
composition boundary.

The target is the real four-byte checked_mem_write with Store.Data,
Supervisor, PBMT_PMA, false aq/rl/con, and the actual present 32-bit payload.
The request retains va=None, translation=(), size=4 and tag=None. Alignment,
actual matched writable PMA region, TOR RAM coverage and disabled HTIF
justify the selected hardware branches; no effective-privilege, virtual
translation or write-announcement wrapper is silently claimed.

The fixed prefix retains five actual register reads: PMA, PMP configuration,
PMP configuration again during address decoding, PMP address, and HTIF.
Its four fractional cells are owned once and restored through the native
RegisterPlan fold. The actual singleton loop, dummy assertion, offset-zero
arithmetic, full-width extraction and eager MMIO/width checks remain in the
proved generated program. No full-register snapshot ownership is required.

OneWrite retains every optional successful response and the error response:
write_ram returns true for every Ok payload and false for Err(), yielding
Ok true/Ok false at the checked wrapper. Permission exceptions are ruled
out by the stated owned-register facts, rather than discarded by a response
assumption. The explicit-privilege metadata wrapper equations retain the
actual callbacks, which reduce purely in this model.

At the real event, Boundary.fold calls the closed native byte-window rule
with n=4 and proves its 2^64 bound internally. Prefix resources, running
context and old reservation survive the register steps; blocked writes
retain them through the native leaf retry. Successful writes return the
new four bytes, same context, unchanged ordinary-view receipt, reservation
None and the four original register cells after exactly one event guard.
The successful `.Ok none` event response is proved by the machine rule,
not supplied by the caller. The only public WP premise is the genuine
final continuation at `.Ok true`; no Boundary/access callback is exported
as an obligation in Spec or nativeSpec.

Independent target rebuild passed **509 jobs**. Fresh strict audit passed
**87 physical declarations in five modules**, traversing all types, opaque
bodies and constructors; only propext, Classical.choice and Quot.sound,
no unsafe/partial dependency, zero exclusions. All five source hashes were
unchanged. Evidence: `/tmp/xv6-lean-research/SupervisorWrite4PeerAudit.lean`,
`supervisor-write4-peer-audit.log`, `supervisor-write4-peer-build.log` and
`supervisor-write4-peer.sha256`.

No correction requested. This is the explicit-supervisor physical checked
store, not an actual virtual store or a whole instruction/function theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
