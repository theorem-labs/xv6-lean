# Independent device ownership review

PASS. All five modules were read against `iris/RiscvPtsto.v:1914–1968`
at the paper pin. UART, PLIC and Virtio assertions each own exactly half of
a native GhostVar for the complete corresponding source state. The public
fragment is the same half assertion, as in the source. Allocation first obtains
full ownership, then splits it into the two half assertions. Agreement and joint
update use native ghost-variable rules, with both halves required. The complete
Virtio state is retained, including durable disk and transient fields.

The combined interpretation and fragments keep all three devices and runtime
names. Focused update lemmas frame the other two authoritative halves and return
the changed device's client half. These are ghost ownership updates, not a claim
that arbitrary device state changes satisfy an operational machine step.

The registry adds distinct slots7,8,9 after the register slot6. Its old/unused
lemmas preserve every slot<7 and>=10. Ledger, views, history and register
capacities are explicitly transported by correct indices; the shared mono-nat
remains slot3. The linked DeviceSpec is supplied by actual checked proofs.

Independent direct replay audited all144 Device declarations including the
private allocation helper, transitively allowing only propext, Classical.choice
and Quot.sound. No production corrections are required.

Replay: `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/DeviceIndependentAudit.lean`

SHA256:
MachCSL/Logic/DeviceDefs.lean 3784ffc2a73b1d8887be8f2a1ae10827ecc402022dde41c778c05b7e706a506b
MachCSL/Logic/DeviceSpec.lean 274e29f75fff893fe77ec1aad9dd10d9d4442675bef34b9c1875c9e6c804c677
MachCSL/Logic/DeviceProofs.lean bb0dd3aa8943140638acbba69d816e826cea093deee41d71fbcd5b1093f47941
MachCSL/Logic/DeviceRegistry.lean 1fa08f87656712eeeb3b188fed1ccfd82a511be14a750f676264c4860195ac0f
MachCSL/Logic/DeviceLink.lean 8ce3b4dff3d3f66e9c3e73af7a2ca83d00a979babf522d0020709a36b1a1c9c2

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
