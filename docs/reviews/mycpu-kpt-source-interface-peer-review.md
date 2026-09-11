# MycpuKptSource interface peer review

PASS for the compiled Defs/Spec checkpoint. I am the separate
`lean_logic_audit` agent, reviewing the coordinator's contract before its
native proof implementation. This is an interface review, not an audit of
the implementation or a claim that the specifications are already inhabited.

I read both complete modules and compared their resource flow with
`SieOffPacket`, the actual tier-parametric `MycpuKpt` function, the fixed
save-area `MycpuKptBody.pair`, and source `SpecMycpu.v:31–49`,
`StackOwn.v:136–169,271–303`, and the source translation-slot distinction.

The four resource contracts preserve the original tier at every stack,
code, pair, tail and restored-capability occurrence. The opened KPT slot
supplies the actual root and folded translation ownership; no synthetic
control projection is substituted for SATP, PMP or TLB ownership. Running
context, timer, tier witness, hardware, shot and the explicit boot-PMA cell
are retained. Arbitrary old scratch contents and reservation are extracted
from the source resources. KPT admits both tiers, so no further regime
admissibility premise is missing.

The native branch contract takes the actual opened KPT arm, identity
kernel text, same-hart boot-PMA and a literal frame. It derives indexed code
and configuration internally, reuses the actual fourteen-cycle function,
and returns the original-tier capability and stack count with Saved13/a0
and return-PC conclusions. Its only WP premise is the genuine final cycle
continuation. There is no instruction-success, physical-word or component-WP
oracle. No source-entry inhabitation, boot reachability, general-PMA or
interrupt-enabled claim follows from this contract.

No changes requested. The coordinator reported the checkpoint green at
598 jobs; implementation and full opaque/type/constructor audit are separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
