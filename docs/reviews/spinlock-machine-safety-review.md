# Independent review of closed spinlock machine safety

Reviewer: OpenAI Codex subagent `lean_logic_audit`, independently reviewing
coordinator-authored `SpinlockBootHandlerProofs`, `SpinlockBootHandlerLink` and
`SpinlockMachineSafetyProofs`.

Result: **PASS for the stated safety conjunct**. The boot handler distributes
the exact all-eight register, reservation and positive code-share resources,
uses the universal actual-BootFacts family for each hart, and invokes the
native cyclic WP. Initial register splitting retains both pin tokens for PLIC.
Fresh lock resources are allocated per boot; persistent idle scenery is shared
without duplicating full counter or holder resources.

The three actual worker forks receive implemented UART, PLIC and reset-disk
WPs. The UART rule retains the established UART/observation namespace
condition; the lock namespace is concrete sibling 4 beside siblings 0–3.
Reset Virtio is obtained from the actual boot facts, preserving the previous
durable medium. Fork order is exactly eight harts followed by UART, disk and
PLIC. Unused affine client fragments may be discarded after initialization;
the authoritative full machine interpretation remains with native WP lifting.

The concrete link discharges all worker contracts on the existing 26-slot
FsTop registry. The initializer uses the very native invariant world provided
by adequacy. `safe_sized` then applies the previously reviewed strong adequacy
adapter to every finite actual pool execution starting at `[power]`, for any
platform and powered-off generation-zero initial state. No boot-handler,
resource-update, ghost-token, chosen-schedule or extra preservation premise
remains. `safe` chooses zero disk fragment bookkeeping size; it does not replace
or restrict the actual durable disk. The initial-state helper gives satisfiable
initial conditions, and the existing concrete Platform inhabitant is available.

`SafeConfiguration` means each actual final thread has a real successor and
the actual observation trace satisfies `ObservationsOK`. The proof does not
use a vacuous postcondition on machine values. This closes safety only:
operational holder-window exclusion and the required interference execution
are still separate obligations, accurately stated in the theorem comment.

Validation: combined replay with CodeIntegrity passes 609 jobs. A fresh
physical-origin audit checked all 11 declarations across the three files and
the full type/body/inductive-constructor dependency cones, with only
`propext`, `Classical.choice` and `Quot.sound`. Zero runtime companions were
excluded; no unsafe/partial dependency was found. Evidence:
`/tmp/xv6-lean-research/SpinlockSafetyPeerAudit.lean` and
`/tmp/xv6-lean-research/spinlock-safety-peer-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
