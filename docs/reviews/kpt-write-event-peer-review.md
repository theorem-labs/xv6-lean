# Independent shared conditional PTE write review

PASS for the six KptWriteEvent modules. The Codex coordinator wrote the
Defs/Spec interface and reviewed the independently implemented slot, update,
event and linking proofs against the fixed contract and source
HartSKpt.kpt_leaf_write_node. The implementer independently reviewed the
interface before beginning proofs.

The arbitrary-mask resource update obtains the current leaf through
canonical snapshot agreement. The proposed word is proved to be an actual
A/D variant of that leaf. Its byte membership and unchanged allowed sets
are derived from the source leaf-family laws. The native full heap and TSO
update retains the original per-byte floors, bounds and publication anchors.
The complete tree is reconstructed with exactly one changed leaf, while
the complete mapping specification and canonical ghost snapshot are preserved.
The map authority and all other physical slots are returned to the invariant.

The public rule invokes the actual conditional-event WP with the caller's
owned reservation snapshot. Native validity supplies the physical reserved
read fact and proves the successful response; the invariant update itself
requires only the already established canonical family. No extra equality
or successful-write premise is assumed. The event's single later is paid
before restoring the top mask and opening the invariant for the update.
No invariant is held across a Sail event. Blocked retries are inherited
from the native rule, and the successful continuation receives the cleared
reservation, positive authored log time and matching view receipt.

Build passed 742 jobs. A fresh coordinator audit checked all18 physical
declarations and full type/opaque/constructor cones with exporting disabled:
standard three axioms only, no exclusions or unsafe/partial dependencies.
Evidence: KptWriteEventRootAudit.lean and kpt-write-event-root-audit.log under
/tmp/xv6-lean-research. Native/registry links discharge all ownership laws.
Complete shared A/D and translation composition remain separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
