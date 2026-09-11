# Supervisor PMP peer review

Decision: pass for the actual TOR-entry grant subprogram. The coordinator read all three implementation modules, the complete approved boundary, source SmodePte.v:31–163 and generated PmpControl.lean:211–354/PmpRegs.lean:281–300 at the pinned model revision.

The configuration preserves entry 0's arbitrary lock and irrelevant bits and every later entry. The unsigned upper bound is multiplied by four in unbounded arithmetic. RAM containment proves faithful conversion of the positive access width to 64 bits. The actual program reads configuration twice and addresses once, then returns through the first loop iteration's early-return channel. The proof neither replaces the loop nor pays for fictitious security/privilege reads. Fetch, PTE load, data load and data store permissions match their exact generated constructors.

The configuration is a pure predicate; the two native register cells in source pmp_config still require ownership packaging. SourceConfig's surrounding security and current-privilege fields are explicit and unused by this subprogram. The arbitrary natural-index helper makes no claim about negative source indices. Translation, PMA, initialization of TOR, and the complete supervisor function WP remain open.

Fresh coordinator audit: all 70 physical declarations are included in the combined 177-declaration audit over 14 reviewed modules. It traverses types, opaque bodies and referenced inductive constructors, accepts only the three standard foundational axioms, rejects unsafe/partial dependencies and initialization-only snapshot constructors. The single excluded total-recursion runtime companion belongs to context-store bookkeeping, not PMP. Evidence: /tmp/xv6-lean-research/BootstrapContextPmpPeerAudit.lean and bootstrap-context-pmp-peer-audit.log. Agent build: 396 jobs; the independent audit loads those checked artifacts.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
