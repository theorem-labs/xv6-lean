# Unopened source JAL and mycpu caller

The two approved Defs/Spec contracts expose native source contracts without
caller-selected translation regimes. `JalSconf` covers actual JAL x1;
`MycpuCallSconf` composes that cycle with the already proved tier-generic
mycpu body. Each has one native contract and no new pure specification:
Bare admissibility, modular return-PC and Saved13 composition reuse the
existing proved MycpuSconf/MycpuCallKptSource facts directly.

The source boundaries are `WpSconfCtl.v:237–281` for JAL and
`SpecMycpu.v:58–78` / `ProofMycpu.v:320–353` for the callable function.
Both retain the disabled-SIE, destination-x1 specialization and explicit
same-hart boot-PMA ownership. They make no new source-entry or boot
inhabitation claim.

`JalSconf.input` owns the unopened actual source capability and pc_is,
JAL code at the original tier, boot-PMA and an arbitrary caller frame.
TargetEven is the sole additional pure condition; JAL needs no minimum
stack depth. The implementation opens SieOffPacket once, obtaining actual
slot resources, Ambient and Admits. Bare admissibility proves the original
tier is identity, so the actual identity code supplies BareJalSource.
KPT supplies KptJalSource at the unchanged original tier. Identity cannot
be routed by tier alone; both of its actual slot arms are handled. Full
tier excludes Bare by the proved admissibility fact.

Both branch results close an unopened source capability at the exact
target with only x1 updated to PC+4. The original tier, stack count,
code/PMA and caller frame return. The only WP input is the genuine
post-JAL cycle continuation, quantified over every actual next clock
choice. No root, synthetic Config, physical instruction bytes, decoder
result, successful translation, branch WP or selected successor is an
input to the public native contract.

`MycpuCallSconf.input` adds identity kernel text to that source/code/PMA
packet. Its pure requirements are n≥2 and the exact JAL target equalling
the actual mycpu entry. Native code ownership supplies PC alignment;
existing pure results derive TargetEven and that low-bit-clearing the
return link leaves PC+4 unchanged. The JAL continuation runs published
MycpuSconf at the same tier, with the original JAL code framed. Its final
source capability returns at PC+4 with Saved13 and a0 computed from the
original pinned TP. Code, identity text, boot-PMA and arbitrary caller
frame are all restored. Both intermediate and final clock choices remain
universal; no successful function or per-step WP is assumed.

The frozen module manifests are `JalSconf{Defs,Spec,Proofs,Link}.lean`
and `MycpuCallSconf{Defs,Spec,Proofs,Link}.lean`, plus their STATUS files.
Internal proof modules accept component specifications for decomposition.
The final native Links supply actual BareJalSource/KptJalSource and the
published MycpuSconf, eliminating every component premise. Both native
Links compile in the combined 1,276-job build. Strict audits pass for all
20 and 19 physical declarations, respectively, including full types,
opaque bodies and constructors, standard three axioms, zero exclusions.
No new camera, registry, decoder, function engine or umbrella change occurs.

The completed contracts will still leave general-PMA behavior, arbitrary
JAL destinations, enabled-SIE migration, source-entry inhabitation, boot
reachability and whole-kernel closure separate. Actual call-site code
production can use the independently proved PushOffMycpuCalls resources;
these theorems do not claim that push_off reaches those sites.

Validation: `/tmp/xv6-lean-research/source-call-dispatch-native.log`,
`jal-sconf-native-audit.log` and `mycpu-call-sconf-native-audit.log`.
Frozen module and pinned source hashes are recorded in
`source-call-dispatch-native.sha256` and `source-call-dispatch-source.sha256`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
