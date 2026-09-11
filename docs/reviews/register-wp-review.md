# Independent review: native register instruction WPs

Reviewer: Codex coordinator. Read every RegisterWP module, the actual node and
global-step definitions, the underlying era update bridge and native lifting rule.

The three exported rules concern actual dependent generated register events:
owned reads, full-cell writes, and universal typed reads. The first preserves
the supplied fraction; the second updates and returns the full cell; the third
needs no cell because its guarded continuation covers every typed result.
All use actual generation certificates and arbitrary empty-type postconditions.

Existence and inversion proofs cover every actual successor. Current-generation
reads use authoritative agreement; writes update the entire state interpretation
and preserve its exact silent trace. The strict older-generation case derives a
death receipt from the real fixed authority and invokes the reviewed corpse WP.
Current-generation powered-off states are excluded by the started receipt.
Thus a live register operation cannot borrow a dead-thread stutter.

Native step lifting preserves masks, guarded continuations and fork obligations.
The final registry wrappers supply concrete capacities without unproved callee
specifications or a successor-preservation oracle. Independent28-declaration
axiom checking passes with only the three standard axioms.

Review: PASS for these constructor rules. Source resume contexts, hooked and
same-value writes, invariant-opening windows and memory rules remain separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
