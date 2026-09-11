# Independent native spinlock protocol review

Reviewer: coordinator OpenAI Codex, independently reviewing all nine frozen SpinlockProtocol modules. Result: **PASS for allocation, native event callbacks and resource exclusion**.

The invariant owns the actual full lock word and its timestamp. In the free case it also owns the free Lock fragment and full counter word. In the held case the winning CPU's fragment and counter are outside the invariant. The latest lock-write timestamp is separate from the acquisition position, so a failed spinner's write of one does not change the prior holder.

Exclusive read establishes only a binary read result and the event's reservation. It does not transfer the counter. The guarded write callback opens the invariant for the actual write event; the reserved mode's WriteFact supplies current-memory equality with the reserved old word. This excludes the wrong invariant branch. The successful zero case updates the physical byte/TSO ledgers, transfers the native Lock fragment at actual log length+1, and returns that append's authored history receipt and updated CPU view. Its timestamp bound is derived from the existing authoritative TSO interpretation.

The reserved-one case still writes one and returns idle, framing the prior holder and acquisition position. Counter load uses the acquisition view and the owned timestamp to justify every admissible read view. Increment performs exact modular 32-bit addition; its new timestamp is not incorrectly assumed below the acquisition view. The non-draining rw,w barrier preserves the stored phase. Unlock checks owner and position agreement before returning the fragment and counter to the free invariant branch.

Invariant masking and the guarded callback boundaries were checked through the Access types and wrapper proofs. The invariant is closed before the one-event continuation. Allocation consumes the supplied full zero lock/counter words and uses native fresh Lock/invariant allocation. Link reuses the existing registry and invariant world with lock camera24. No native callback remains an assumed client obligation.

Fresh coordinator audit passed all199 physical-module declarations and their full type/body dependency cones, including private helpers: standard three axioms only, zero exclusions and no unsafe/partial dependency. Owner build passed516jobs. Evidence: spinlock-protocol-root-audit.log in the research directory.

Holder-fragment exclusion is a resource theorem. An operational statement about every actual pool execution still needs the concrete annotated-pool simulation, instruction/phase invariants and boot linkage. This review does not close that gate or any whole-system root.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
