# KPT publication barrier interface review

Reviewer: OpenAI Codex, independent lean_logic_audit agent. The coordinator
wrote the reviewed definitions and specifications. This is a signature and
modal-feasibility review, not an audit of the later implementation.

PASS for `KptPublishBarrierDefs` and `KptPublishBarrierSpec`. I read both
complete modules, the native BarrierWP definitions/specification/proofs,
KptPublish's publication and allocation rules, and KptShared.allocate.

The event callback requires only a basic update on the actual heap/TSO
interpretation. Existing `publish_boot` and `publish_view` provide exactly
that transformation while retaining running-context ownership. The map
authority and two pending one-shot tokens remain linear until installation.
The boot route gives a log bound and agent-zero forwarding credential; it
does not claim the publishing CPU has reached global log top. The view route
uses the real draining barrier's own-publication bound and current view.

After the actual event guard, BarrierWP restores the top mask before invoking
its continuation. At that point `ResourceSpec.install` can allocate the
shared invariant using existing `KptShared.allocate` and consume its fancy
update through native `fupd_wp`. No fancy-update allocation is incorrectly
required inside the basic ghost callback, and no invariant remains open
across a physical event. Allocation itself supports arbitrary masks; unlike
opening an invariant, it does not require an extra namespace-subset premise.

The final contract supplies actual client resources and a guarded genuine
continuation. It assumes neither a publication callback nor the desired
kernel-tier tree. Actual boot reachability, full supervisor capabilities and
whole-function correctness remain separate. No signature correction found.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
