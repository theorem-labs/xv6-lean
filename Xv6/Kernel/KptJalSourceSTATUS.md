# Source KPT JAL branch

FROZEN NATIVE: five modules Defs/Spec/Pure/Proofs/Link GREEN1,172 jobs.
All three pure contracts and the resource/cycle composition are proved.
The final nativeSpec supplies KptJal.nativeSpec internally; no component
interface or selected-successor premise remains. Registry Link is closed.

The input is the literal opened KPT source arm at either original tier,
actual tier-indexed JAL code, same-hart boot-PMA and caller frame. Only
TargetEven is an additional pure premise; there is no minimum stack depth.
The result preserves the original-tier source capability and all stack
slots, changes only x1 to PC+4, and returns code/PMA/frame at the target.
The only WP premise is the genuine returned-cycle continuation.

The proof reuses actual KptJal.cycle. Its final native Link supplies
that implementation. No branch inference from tier, physical-code substitute,
known fetch result, Config oracle or duplicate translation cells are used.

Design: `docs/design/kpt-jal-source-boundary.md`.
Proof build: Pure1.3 s/Proofs1.5 s/Link1.1 s. Fresh strict audit checked all34
declarations from five physical modules, full type/opaque-body/constructor
cones, standard three axioms only, no unsafe/partial dependency and zero
exclusions. Logs/script under `/tmp/xv6-lean-research`:
`kpt-jal-source-native.log`, `kpt-jal-source-native-audit.log`,
`KptJalSourceNativeAudit.lean`. Earlier conditional31 audit remains recorded
separately; the final audit includes the complete native Link cone.
Bare dispatch, general PMA, enabled interrupts and entry/boot inhabitation
remain separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
