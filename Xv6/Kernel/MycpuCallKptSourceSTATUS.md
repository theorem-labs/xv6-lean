# KPT source mycpu caller at either tier

FROZEN NATIVE: five modules Defs/Spec/Pure/Proofs/Link prove all three pure
and one native contract. Native Link supplies every component implementation.
Initial resources are the actual opened KPT
arm, original-tier JAL code, identity source text, same-hart boot-PMA and
caller frame. Additional pure premises are n≥2 and exact target=mycpu-entry.

The native composition uses KptJalSource followed by the actual
tier-generic MycpuSconf body. It restores the unopened source capability
at PC+4 with unchanged original tier/stack count, Saved13 and a0 from
entry pinned TP, plus all code/text/PMA/frame resources. Only the genuine
final-cycle continuation is a WP premise. Pure return-PC/result laws reuse
the existing MycpuCallSconfKpt proofs; no decoder/function proof is copied.

Design: `docs/design/mycpu-call-kpt-source-boundary.md`.
Native build GREEN1,248 jobs: Pure1.2 s/Proofs1.6 s/Link1.1 s. Fresh strict
audit checked all33 declarations in five physical modules, complete
type/opaque-body/constructor cones, standard three axioms only, no
unsafe/partial dependencies and zero exclusions. Logs/script under
`/tmp/xv6-lean-research`: `mycpu-call-kpt-source-native.log`,
`mycpu-call-kpt-source-audit.log`, `MycpuCallKptSourceAudit.lean`.
Frozen source hashes: `mycpu-call-kpt-source-frozen.sha256`.
Bare caller dispatch, general PMA, enabled interrupts and source/boot
inhabitation remain separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
