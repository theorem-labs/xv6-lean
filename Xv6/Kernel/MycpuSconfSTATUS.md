# Tier-generic source mycpu body

FROZEN: three pure and one native contract are proved in five modules:
Defs, Spec, Pure, Proofs and Link. Both actual branch implementations are
supplied by nativeSpec; no component premise remains. The public input is the unopened disabled
source capability for either tier, identity source text, retained same-hart
boot-PMA and caller frame, with scratch depth at least two.

Implementation opens the actual source slot once. Bare admissibility
forces identity and invokes MycpuBareSource; KPT invokes MycpuKptSource at
the original tier. Both actual fourteen-cycle functions restore the source
capability/stack count, Saved13/a0 result, return PC and all caller resources.
No regime, Config, root, physical-word, component-WP or success premise
survives the final native interface. Its only WP premise is the genuine
returned-cycle continuation for every next clock choice.

Source mapping and limitations: `docs/design/mycpu-sconf-boundary.md`.
Native build passed 1,222 jobs, dispatcher proof and Link 1.3 s each.
Fresh strict audit checked all 35 declarations from five physical modules,
full type/opaque-body/constructor cones, standard three axioms only,
no unsafe/partial dependency and zero exclusions. Logs/script under
`/tmp/xv6-lean-research`: `mycpu-sconf-native.log`, `mycpu-sconf-audit.log`,
`MycpuSconfAudit.lean`. The coordinator's KPT branch was independently
reviewed and audited (55 declarations) before linking.
General PMA, enabled SIE/migration, source-entry inhabitation, boot
reachability and call-site composition are separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
