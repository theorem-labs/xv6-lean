# Independent hart restart WP review

Reviewed `RestartWP{Defs,Spec,Proofs,Link}.lean` and status against pinned `RiscvExec.v:1007–1031` and the actual restart `NodeStep`/global `Step` constructors. Result: **pass for the declared restart-rule scope**.

The successor inversion quantifies both clock choices; the false choice is used only to witness reducibility. Every live transition clears exactly the current CPU's reservation. The ghost proof consumes its actual fragment, updates the authoritative reservation mirror, proves the remaining reservations still satisfy their invariant, and frames the complete era and fixed machine interpretation. Registers, RAM, devices, durable disk, TSO log and views remain unchanged. The actual silent transition restores the observation interpretation. Stale generations use the proven actual dead-step rule and its guarded WP.

The continuation is under a later and must handle every clock choice with a `none` reservation fragment. `wp_restart_fragment` preserves the source's explicit old-fragment contract; the core existential-fragment form is a proved packaging generalization. The independent spec and 23-slot registry link retain that continuation and discharge component ghost/state specifications. Neither a complete generated cycle nor a kernel safety theorem is claimed.

Validation: independently replayed `/tmp/xv6-lean-research/RestartWPIndependentAudit.lean`; all 21 namespace declarations and transitive proof cones use only `propext`, `Classical.choice`, and `Quot.sound` (count in `restart-wp-independent-axioms.log`). The owner's successful build was inspected. No source files were changed during review.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
