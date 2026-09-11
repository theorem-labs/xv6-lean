# Independent review: native exclusive RAM read

Verdict: PASS. Codex root read all four MemoryExclusiveWP modules, exact
HartEvents.v exclusive leaf and swp contract, and the actual node-step branches.
The complete dependent request and all Nat widths survive the direct-node API;
RAM/exclusive guards are explicit. The generalized source mctx/swp interface is
accurately left outside this layer.

Blocked reads retain their cursor and view, clear only the caller's reservation,
and use guarded retry at an existential reservation value. Successful reads use
the actual current flat memory, advance exactly to log length, install the exact
snapshot and return the real Ok(word,none). Inversions cover all actual live
successors; stale generations use the existing dead-thread rule. Conflicts come
from all other actual CPU reservations. The callback restores the same complete
register/heap/device bundle and advanced TSO interpretation; the rule frames
and restores durable disk, reservation authority/validity, fixed names and
observations. A native view receipt is supplied only on success.

The concrete byte-window rule uses actual heap agreement, requiring neither
pristine timestamps nor a fictitious earlier-view read. Held-snapshot readback
derives submap from reservation agreement and ReservationsOK; only its adapter
uses the exact source n<2^64 bound to recover all byte positions. That bound is
absent from the generic exclusive-read rule, including zero and modular widths.
The shared-capacity link allocates no extra authority or invariant world.

Fresh combined build with snapshot-byte modules passed. A separate physical
origin audit checks all 45 declarations and their full type/body dependencies,
including private helpers: only propext, Classical.choice and Quot.sound;
no unsafe/partial semantic dependencies and zero exclusions. Records:
/tmp/xv6-lean-research/MemoryExclusiveWPRootAudit.lean and exclusive-root-audit.log.
This is the native event leaf, not an AMOSWAP instruction or lock theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
