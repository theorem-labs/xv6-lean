# Disabled source JAL: KPT branch at either tier

The compiled native `KptJalSource` composition generalizes the existing
full-tier `KptJalSconf` resource adapter to the actual opened KPT arm at
either original source tier. It preserves the tier on stack, code,
witness and restored source capability. It introduces no instruction engine
or additional translation ownership.

The source target is `WpSconfCtl.v:237–281`, `wp_jal_s_sconf`, specialized
to destination x1 and disabled SIE. Source premises require a nonzero,
permitted destination and even target; x1 discharges the destination facts
without changing SP or pinned TP. The native input supplies the actual
JAL code and target-even condition. Code ownership yields PC alignment,
which internally establishes the encodable immediate. No caller supplies
a decoder result, successful translation or arbitrary Config.

Input contains an existential actual root/control, the Ambient facts
derived when opening the source packet, and its literal opened KPT arm.
It also owns `KptJal.code` at the original tier, the retained same-hart
boot-PMA cell, and a caller frame. Both identity and full tiers admit KPT.
This is a branch contract, not a theorem that a tier alone selects KPT.

The implemented adapter obtains the native configuration and generation certificate
from those resources. It passes the existing fifty-cell source packet,
folded KPT residue, actual running context and extracted reservation into
`KptJal.cycle`. All source stack slots remain in `sourceFrame`, alongside
the same-tier witness, timer, whole hardware assertion, shot and caller
frame. JAL requires no scratch stack minimum and the stack is never split
or reindexed. The native cycle internally performs actual fetch/decode,
JAL, clock/retirement and restart, preserving fetch guards and handling all
allowed native results. The source adapter introduces no per-step oracle.

The resulting file is exactly `HartTp.set file 1 (PC+4)`, at the actual
JAL target. Three pure contracts preserve SP and Saved13 and derive the
source Boundary from the actual `Completed` relation. The native proof
closes the original-tier source capability, returns all code/PMA/frame
resources and invokes only the genuine final-cycle continuation, for every
next clock choice. It does not expose its internal successful step as a
caller premise.

Five frozen modules: `KptJalSource{Defs,Spec,Pure,Proofs,Link}.lean`, STATUS
and this design. All three pure contracts and the native composition
compile at 1,172 jobs (Pure1.3 s/Proofs1.5 s/Link1.1 s). The private
`wp_cycle`/`actual` parameter is supplied by KptJal.nativeSpec in the final
Link. Both nativeSpec and registrySpec have no remaining implementation
premise. Existing full-tier adapter, families and umbrellas remain unchanged.

Fresh strict audit checked all34 declarations from five physical modules,
full type/opaque-body/constructor cones, standard three axioms only,
no unsafe/partial dependency and zero exclusions. Logs/script under
`/tmp/xv6-lean-research`: `kpt-jal-source-native.log`,
`kpt-jal-source-native-audit.log`, `KptJalSourceNativeAudit.lean`.
The earlier conditional four-module checkpoint is preserved separately;
the final audit includes the actual native JAL implementation cone.

The specialization retains disabled SIE, destination x1 and explicit
boot-PMA. It does not establish the Bare arm, unopened-source dispatch,
general-PMA behavior, source-entry inhabitation, boot reachability or
enabled-SIE/migration. Those remain separate boundaries.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
