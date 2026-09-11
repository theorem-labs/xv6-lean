# Full-tier source mycpu wrapper independent review

Reviewer: OpenAI Codex, independent `lean_logic_audit` agent. Reviewed all
five coordinator-authored MycpuSconfKpt modules (Defs, Spec, Pure, Proofs,
Link), the source contract, final STATUS/design and the entry/text resource interfaces. The
reviewer implemented the separately reviewed MycpuKpt function dependency;
this is an independent review of the coordinator's wrapper composition.

PASS for the stated full-tier, disabled-interrupt, boot-PMA specialization.
The final Link constructs both public specs from actual proofs; no component
interface, execution success or per-instruction WP is a public premise.
The source comparison covers SpecMycpu.v:26–52, ProofMycpu.v:62–318 and the
complete thirteen-key CalleeSaved.v:34–48 predicate at the pinned source.

The implementation starts with the actual SieOffPacket capability and pc_is,
identity kernel text, retained discarded same-hart pmaBoot cell and frame.
Native text monotonicity/window production derives the fourteen full-tier
fetch windows while retaining the original text. Native Entry obtains the
root, configuration, arbitrary initial scratch words and reservation, and
its hardware resource supplies the generation certificate. The full
fifty-cell packet and separately folded KPT residue are passed once to the
actual MycpuKpt function.

The literal frame carries the untouched stack tail, timer, full-tier
receipt, hardware, publication shot, PMA and caller frame across the whole
function. Return restoration uses the proved SP equality and source
Boundary; Entry rejoins the same anchored RA/S0 words with that tail and
restores the original free-stack count and disabled capability. The returned
pc_is is the actual low-bit-cleared original RA. The thirteen software saved
keys and a0=mycpuRet(entry pinned TP) follow from the function result's
proved mapOther/value fields. The TP interpretation remains source ownership
at disabled SIE, not an invented persistent register fact.

All fourteen event-receipt bundles remain available from the underlying
function. The wrapper does not expose them in the smaller source contract;
its affine native proof may forget them. Original kernel text, PMA and the
caller frame are returned. The final continuation is the genuine next cycle
for every next clock choice. No trap-handler, translation-success, component
WP or physical-stack oracle is introduced.

Independent validation rebuilt MycpuSconfKptLink successfully in 1,201 jobs.
A fresh strict audit checked all 32 physical declarations in five modules,
including complete types, opaque values and constructor cones. Only
propext, Classical.choice and Quot.sound occur; no unsafe/partial dependency
and zero exclusions. SHA256 checks confirmed every reviewed Lean file was
unchanged across the build/audit. Research evidence is
`MycpuSconfKptPeerAudit.lean`, `mycpu-sconf-kpt-peer-build.log`,
`mycpu-sconf-kpt-peer-audit.log` and `mycpu-sconf-kpt-peer.sha256`.

This proves the resource-conditional native source wrapper, not satisfiable
allocation of its complete source entry resources or boot reachability.
General source tiers/PMA classes, the callable JAL form, interrupt-enabled
migration and whole-xv6 adequacy remain separate. No code correction was
required. The final STATUS/design correctly records the constructed Link,
32-declaration audit and remaining resource-inhabitation/boot obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
