# UART driver ghost algebra

`UartGhost{Defs,Spec,Proofs,Registry,Link}` port the complete UART ghost
algebra in `WpUart.v:285–605,752–790` and `Xv6Cameras.v:343–353`, at paper
pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The native MonoList camera tracks accepted bytes and transmitted bytes at
two explicit runtime names, sharing one capacity. Persistent prefix
receipts, authority update and stability match the source. The transmitter
uses exact half GhostVars over the accepted list. DLAB uses the source
DFracAgree Bool camera, including a discarded false fragment and the
half-to-discarded freeze. The authority/client halves are jointly required
for a change; no writable fragment is retained by freezing.

All four source ghost quantities occur in `ghosts`. Allocation starts at
an arbitrary actual UART state, returns both trace authorities, transmitter
and DLAB authority halves, and all three source initial client resources.
In particular DLAB is allocated at its ACTUAL value, not assumed false.
Accepted-byte receipts do not claim that bytes have reached the wire.
The source THRE poll and future-ready theorems use transmitter agreement,
the transmitted-prefix lower bound, and frozen DLAB ownership; no other
hart's code is assumed. The two actor helpers preserve all four quantities
across actual receive steps and grow the transmitted prefix on transmit,
retaining the source distinction between `out` and the loopback-aware wire.

The independent specification exposes allocation, receipt, agreement,
update, freeze, stability, poll and readiness. The checked implementation
links at the new explicit registry. Slots 20–22 are MonoList Byte, GhostVar
(List Byte), and DFracAgree Bool. All slots 0–19 are preserved. The accepted
and output names share slot 20; no duplicate trace camera is introduced.
All application capacities, fixed observation slot 11, and native invariant
slots 16–19 are derived explicitly for the extended registry. Allocated
native invariant names are passed separately through `nativeInvariant`.
No cross-registry ownership equivalence is assumed.

`MachCSL/Devices/Plic/Plan.lean` separately adds the exact source
`PlicPlan.v:41–65,117–124` invariant and reset/latch preservation. It ranges
over EVERY Nat context and enable-word index, preserving out-of-range
entries as well. The source mask operands are nonnegative unsigned values;
the bitwise test is represented with Nat bit operations. This is not the
stale comment's narrower S-context-only property.

Validation: the 380-job build of `MachCSL.Logic.UartGhostLink` passes
(proof module 1.1 seconds), and the separate audit passes all 209
namespace declarations using `/tmp/xv6-lean-research/UartGhostAudit.lean`.
Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. No custom
axiom, `sorry`, `native_decide`, or `bv_decide` is used.

Native UART/PLIC invariant allocation, observation permits and the actual
UART loop WP follow in the separate UartWP layer. No complete disk protocol,
combined `dev_inv`, driver operation or final adequacy is asserted here.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
