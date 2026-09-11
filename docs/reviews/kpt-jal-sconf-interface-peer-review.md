# Full-tier source JAL capability interface review

Reviewer: OpenAI Codex, independent `lean_logic_audit` agent. Read the complete
coordinator-authored KptJalSconfDefs/Spec, underlying KptJal definitions and
native contract, and pinned WpSconfCtl.v:237–281. This is a signature and
composition-feasibility review, not an implementation audit.

PASS for the explicit full-tier, disabled-interrupt, JAL-x1 specialization.
The source rule requires a nonzero permitted destination and an even target;
x1 discharges the destination constraints and preserves SP/TP. The proposed
rule retains the actual target-even premise and changes only RA to PC+4 in
the software map. It preserves the original free-stack count without an
unnecessary two-word minimum, since JAL consumes no stack word.

The input owns actual source capability/pc_is, the native four-byte JAL code
resource, explicit same-hart discarded boot-PMA cell and frame. Code supplies
PC alignment, so target parity can establish the immediate's encodability
internally. The actual fetch still admits its one/two chunk paths and native
shared-translation effects; the interface does not supply a decoder or
translation-success certificate. The target's code is left to the genuine
post-jump continuation, as in the source rule.

The boundary contract preserves source control fields through actual
Completed and derives both PC and nextPC at PC+signExtend(imm). The final
source capability carries the deterministically updated RA map, original
stack count, code/PMA/frame, and the real next cycle for every clock choice.
No configuration, root, reservation value, per-step WP or success oracle is
a public premise. The underlying native KptJal cycle must be supplied in the
final Link before implementation closure is claimed. No signature change
is required.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
