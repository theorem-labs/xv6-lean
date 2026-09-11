# Timer capability native peer review

PASS. Codex's artifact audit agent independently reviewed the complete
coordinator-authored `MachCSL/Logic/TimerCap{Defs,Spec,Proofs,Link}.lean`
implementation, its status/design and the complete 113-line source
`iris/TimerCap.v` at paper pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. No correction was requested.
This completes the implementation review beyond the earlier signature-only
report.

The exact source capability remains a discarded same-hart `mcounteren`
cell whose TM bit is one, together with an invariant at `nroot.timer`
containing full ownership of `stimecmp` at an arbitrary deadline. Both use
the explicit same era/CPU register name. The implementation does not add
deadline semantics, an STCE premise, or a fictitious current-register
observation.

All four approved contracts are constructed natively. Deadline introduction
retains the supplied value. Enabled introduction invokes the actual
GhostMap-backed register persistence rule, consuming the supplied fraction
and retaining the same value at the discarded fraction. Enabled agreement
uses two actual fragments for the same dependent register key and derives
value equality through native GhostMap agreement. It requires the caller's
real fragment; the persistent capability alone does not establish a
physical register value.

Capability introduction first freezes the supplied counter ownership, then
uses native `inv_alloc` on the actual full deadline cell. The required later
is introduced in its body proof. Allocation at an arbitrary mask matches
the native and source allocation theorem; no namespace-in-mask premise is
needed until an invariant is opened. No register authority or new camera
is allocated. The native link discharges the complete Spec using the
supplied actual register and invariant capacities, with no implementation
oracle.

The five instances have the correct scope: enabled is persistent and
timeless, deadline is timeless, and deadlineInv and capability are
persistent. The full existential deadline cell itself is not made
persistent. The invariant is still indexed by the original era and CPU.

Independent build: `python3 tools/lake.py build MachCSL.Logic.TimerCapLink`
with `/data/jason/.elan/bin` prepended to PATH passed 352 jobs. A fresh audit
with exporting disabled covered all 27 physical declarations in four
modules, including private helpers, and checked full types, opaque bodies
(`allowOpaque := true`) and constructors. Only `propext`, `Classical.choice`
and `Quot.sound` occur; no unsafe/partial dependency and zero exclusions.
Evidence: `/tmp/xv6-lean-research/TimerCapPeerAudit.lean`,
`timer-cap-peer-build.log` and `timer-cap-peer-audit.log`.

This is conditional capability construction from owned registers, not a
timerinit, CSR execution, migration or boot-inhabitation theorem. Those
source consumers remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
