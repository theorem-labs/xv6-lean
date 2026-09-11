MycpuKptSource: native KPT arm for either source tier

Five modules Defs/Spec/Resources/Proofs/Link compile across 1,204 jobs.
Four resource contracts and one native full-function contract are implemented.
The approved interface preserves the original source tier everywhere; no
identity-to-full conversion loses stack mapping information.

Input is the literal opened KPT arm of SieOffPacket, identity kernel text,
an explicit same-hart boot-PMA cell and caller frame. Configuration,
certificate, root and arbitrary save words are obtained from that ownership.
The actual fourteen-cycle native function constructs all execution phases
and returns saved-register/CPU-address results. The exact same source tier,
stack count, timer, translation shot, hardware and caller frame are restored.
Native Link supplies every component implementation.

Fresh strict audit passed all 55 declarations in the five modules, with
complete physical/type/opaque/constructor traversal, standard three axioms
only and zero exclusions. Independent full implementation review and a
second fresh 55-declaration audit passed with the same strict boundary. The tier-generic unopened-source dispatcher is separate, as
are boot reachability, source entry inhabitation and whole-system closure.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
