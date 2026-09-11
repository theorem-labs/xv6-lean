# Timer capability interface peer review

PASS for the coordinator-authored `MachCSL/Logic/TimerCap{Defs,Spec}.lean`
checkpoint. Codex's artifact audit agent independently read both modules
and the complete 113-line `iris/TimerCap.v` at paper pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. This is an interface review;
native implementation proofs are a subsequent review scope.

The definitions preserve the exact source predicates: an existential
32-bit `mcounteren` value owned at the discarded fraction with TM equal to
one; an existential, arbitrary full 64-bit `stimecmp` cell; the latter
under the source `nroot.timer` invariant; and their separating conjunction.
Both registers use the same explicit era and CPU register name. There is
no invented deadline relation or cross-hart capability.

The four contracts correctly expose deadline introduction, persistence
from any original register fraction, capability allocation at an arbitrary
mask, and agreement with a supplied actual same-register fragment.
The last law does not infer a machine register value from a capability
alone. The generated TM accessor is used directly. Persistence of the
enabled predicate and capability is an expected native implementation
instance. The signatures require the real native invariant capacity and
do not assume a new camera or fabricated invariant allocation.

The signature checkpoint built successfully in the independent combined
666-job Stack/Timer build, recorded at
`/tmp/xv6-lean-research/kernel-stack-peer-build.log`. No separate proof-cone
audit or completed native implementation is claimed by this report.
Source timer initialization, STCE/SConf setup, timer CSR execution and
deadline behavior remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
