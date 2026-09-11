# Tier-generic disabled source mycpu body

This boundary removes caller-selected translation regimes from the native
source body contract. It reuses the actual fourteen-cycle Bare and KPT
functions through their source resource adapters. All three pure contracts
and the native dispatcher are implemented, with both actual branch
implementations supplied by the final Link.

The target is `SpecMycpu.v:31–49`: at disabled SIE and scratch depth at
least two, source `sie_cap_gpr`, identity `kernel_text` and entry `pc_is`
fund actual execution, restoring the same capability/depth at the original
RA's low-bit-cleared return target. The result preserves exactly the thirteen
source callee-saved entries and sets a0 to `mycpu_ret` of the entry pinned
TP. As explained in the source comment at lines21–30, this is the disabled
same-hart contract; migration and enabled-SIE continuation ownership remain
outside this theorem. The explicit retained same-hart boot-PMA cell is the
current native specialization, beyond the source's general PMA-class facts.

`MycpuSconf.input` owns the unopened source `SieOffPacket.input` at an
arbitrary original tier, identity kernel text, boot-PMA and a literal caller
frame. No regime, root, synthetic register configuration, physical word,
opened resource packet, component WP, successful response or execution
witness is required. The only WP premise is `finish`, the genuine returned
cycle continuation for every actual next clock choice.

The proof opens `SieOffPacket` exactly once, obtaining an actual regime,
ambient facts, the admissibility fact and its native resources. For Bare,
the proved pure admissibility case forces identity tier. It packages that
same opened arm for `MycpuBareSource.nativeSpec`, which extracts actual
SATP/PMP ownership, derives the physical code and stack with retained mapping
closures, executes the proved Bare function, and restores identity source
ownership. For KPT, it packages the same opened arm for
`MycpuKptSource.nativeSpec`; both identity and full tiers remain possible.
That adapter derives code from source text at the original tier and restores
that tier after the actual translated function. No TLB cell is added to
Bare and no translation resources are duplicated across branches.

Both postconditions yield the identical public Saved13/a0 fact, original
stack count, running context and disabled source capability, return PC,
identity text, boot-PMA and caller frame. The private composition is
parameterized by the two component specifications to keep modules separate;
the final Link supplies both actual native implementations. No such
parameter survives `nativeSpec` or `registrySpec`.

The frozen files are `MycpuSconf{Defs,Spec,Pure,Proofs,Link}.lean`, STATUS
and this design. Three pure contracts cover Bare-tier admissibility and
the two branch result conversions; one native contract is the actual body
rule. Existing `MycpuBareSource` and coordinator-owned `MycpuKptSource`
files remain unchanged. There is no new camera, registry slot or engine.

Remaining scope after this theorem includes general-PMA operation,
interrupt-enabled migration, source-entry resource inhabitation, boot
reachability and call-site JAL composition. This contract does not assert
those outcomes. Source proof portability and full-model correspondence
remain tracked separately by the repository's established audit policy.

Validation: final native Link GREEN 1,222 jobs (dispatcher proof 1.3 s,
Link 1.3 s). A fresh strict audit checked all 35 declarations from five
physical modules through full types, opaque bodies and constructors.
Only `propext`, `Classical.choice` and `Quot.sound` occur, with no
unsafe/partial dependencies and zero exclusions. Script/logs under
`/tmp/xv6-lean-research`: `MycpuSconfAudit.lean`, `mycpu-sconf-audit.log`,
and `mycpu-sconf-native.log`. The KPT branch implementation separately
passed this agent's full five-module review and 55-declaration audit.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
