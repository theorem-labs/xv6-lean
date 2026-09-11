# Independent power-worker WP review

Reviewed `PowerWP{Defs,Spec,Proofs,Link}.lean` against pinned `RiscvAdequacy.v:624–935`, the actual `Machine.Step.power` constructors, and the already reviewed fixed observation invariant. Result: **pass for the explicitly conditional machine-level scope**.

The native guarded proof handles both actual power transitions. It updates the fixed observation authority through invariant-held client custody, then uses the actual transition to restore trace alternation, generation counts, and UART wire agreement. Power-off preserves the durable disk through the existing proved state update. Power-on allocates a complete machine era from every allowed `BootFacts` successor; the finite memory encoding is tied back to the actual successor RAM. The universally quantified, persistent boot handler must pay the WPs of all eleven actual forked workers and receives the actual generation certificate and all allocated machine boot-client resources. Neither a particular favorable boot successor nor a scheduler is selected.

This is not the complete source `wp_power_loop`: source crash predicates, disk projection/custody/lending hooks, kernel auxiliary ghost resources, and general observation-ledger hooks remain outstanding and are explicitly excluded by the current status. The trivial shared observation invariant is a concrete trace-custody specialization, not a proof of the paper's UART or crash-safety policy. The boot handler remains a substantive caller obligation; the registry link does not erase it.

Validation: independently replayed `/tmp/xv6-lean-research/PowerWPIndependentAudit.lean` through `python3 tools/lake.py env lean`; all 13 namespace declarations and their transitive axiom cones use only `propext`, `Classical.choice`, and `Quot.sound`. The producer's successful module build was inspected; no source changes were made during this review.

*Authorship note: this was researched and written by an AI coding agent (OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is posted from this account.*
