# Native KPT publication barrier: independent review

PASS for the declared five-contract boundary. Codex subagent artifact_audit
independently read the coordinator-authored four frozen modules
Xv6/Kernel/KptPublishBarrier{Defs,Spec,Proofs,Link}.lean, design and status;
no implementation change was requested. This is separate from the
coordinator's own source review/audit and from earlier Fable reviews.

Source comparison used paper pin fa7f0a01c4b40489fac8ad303f079c2dfc7a1476:
HartBarrier.v94–184/204–308 (pub_step, ghost_step and actual guarded leaves),
KptPublish.v272–296/534–551 (physical publication outputs), and the native
KptPublish/BarrierWP interfaces and implementation that this composition
calls. Both source routes retain hartAgent cpu=0. The boot route derives
only the actual log-length bound; its True receipt does not claim a view.
The draining route uses the actual post-fence own-publication bound and
returns the current hart view receipt, without inferring global log top.

The input owns the actual full user-tier depth-two tree, running context,
map authority and both unset tokens at the same era names. protocol_boot and
protocol_view discharge their heap/TSO callbacks by the existing native
physical conversion, with the heap interpretation equality checked by rfl.
The exact same heap and TSO state are restored. The map and unset resources
remain framed until installation; neither a replacement tree nor physical
truth inferred solely from map authority is supplied by a client.

install consumes that published tree/map/two tokens through native shared
allocation and returns the actual shared invariant, snapshot, bound and
credential. For the boot CPU the credential is correctly derived from the
log receipt, not fabricated from a missing view receipt. Both WP proofs
apply the actual barrier constructor with its actual continuation and single
guard. Their shared allocation occurs via fupd_wp at top *after* the guarded
event update, not inside the basic heap/TSO update or while the step mask is
empty. The underlying leaf preserves the whole state interpretation/trace,
and its dead-generation case retains the actual dead-thread behavior.
All native/registry Link fields are discharged without component or
publication callbacks in the public theorem premises.

Independent validation:

- Build Xv6.Kernel.KptPublishBarrierLink: 731 jobs, exit0.
- Fresh audit: every57 physical declaration in all4 modules, including
  private helpers, exporting disabled, collectAxioms plus complete types,
  opaque bodies (allowOpaque=true) and inductive constructor traversal.
  Only propext/Classical.choice/Quot.sound; no unsafe/partial dependency;
  zero exclusions.
- Evidence: /tmp/xv6-lean-research/KptPublishBarrierPeerAudit.lean and
  kpt-publish-barrier-peer-{build,audit}.log.

This composition does not establish an actual decoded fence call site,
construct/allocate its input table resources from boot, install SATP, or
inhabit the source supervisor capability. Its continuation WP remains the
ordinary real program obligation. These limits match the design and status.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
