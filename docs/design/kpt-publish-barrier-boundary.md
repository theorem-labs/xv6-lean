# Physical publication at an actual machine barrier

This component connects the proved KptPublish physical ownership conversion
to the existing BarrierWP event rule. It retains the supplied full user-tier
depth-two tree, map authority and two pending names at the same era. It does
not construct a table or assert reachability of this input from boot.

The boot route works at any actual barrier and derives the bound from the
actual log length. The view route requires fenceDrains and derives the bound
from the actual post-barrier CPU view. Both retain the existing publication
rule's hartAgent cpu = 0 premise. The draining rule supplies only the CPU's
own-publication bound, not a global log-top view.

The event's callback is a basic update over the exact heap and TSO state.
It converts physical ownership and restores both interpretations. It cannot
allocate a shared invariant there. A separate fancy-update rule consumes the
published tree and pending names to allocate the existing shared invariant;
the actual barrier WP runs this allocation in its continuation after the
single event guard. Output includes the same running context, shared tree,
canonical snapshot, bound, log receipt and genuine boot/view credentials.

Two protocol, one resource and two native WP contracts are explicit. Clients
supply no physical-state interpretation, ghost-update callback, replacement
tree, successful barrier response or continuation before the real event.
The continuation after publication remains the ordinary program WP premise.

The native BarrierWP leaf was already implemented and independently reviewed
before Fable rounds nine and ten; its Proofs/Link files were absent from those
review snapshots. This bridge is additional composition at the actual event.
A decoded sfence call site, physical boot table construction and the complete
source supervisor capability remain separate consumers.

Defs/Spec checkpoint: 415 jobs; independent interface review passed. All five
contracts now have native proofs and complete Link constructors. Full build
passed 731 jobs and strict audit covered all 57 declarations in four modules,
with the standard three axioms only and zero exclusions. The final WP proof
uses the existing fupd_wp rule at top inside the actual guarded continuation.
No new camera, axiom or era-name allocation is introduced.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
