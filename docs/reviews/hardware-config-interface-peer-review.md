# Hardware configuration: independent interface review

PASS for the actual HardwareConfigDefs/Spec checkpoint. Codex subagent
artifact_audit independently compared both complete coordinator-authored
files with pinned RiscvFetchExec.v275–338. All six frozen hardware cells,
eleven source facts, two existential frozen counter cells, static identity
mapping claims and generation certificate are retained. The Values grouping
moves the counter existentials outward without fixing their values.
mcounteren remains outside this bundle, as the source requires.

The constructor consumes actual eight-cell ownership before discarding it;
no synthetic reference file proves ownership. The source MISA/security
constants are explicit facts. The typed agreement fields require a real
additional register cell; static claims require the exact Static predicate.
No new camera, boot initialization or native allocation is inferred.
This is signature review only, before native proofs and their separate audit;
the pure boot fact depends on the separately checked native PMA classifier.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
