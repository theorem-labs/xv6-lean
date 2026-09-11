# Independent era/device update review

Result: **PASS for the declared resource-update scope**. Read all four
`EraDevices{Defs,Spec,Proofs,Link}.lean` files and checked the source
`RiscvPtsto.v:1913–1968`, `2083–2095`, and `2150–2226` at paper pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The source UART, PLIC and Virtio interpretations use two native half
GhostVars per runtime name, with agreement and joint updates. The new
bridge reuses those exact capacities and the complete actual device state.
`devices_access` exposes the existing three-device interpretation and a
reassembly wand. The wand explicitly requires equality of the new and old
Virtio durable-disk functions: that equality is necessary to frame the
separate per-era disk-image authority. The other era conjuncts depend on
registers, RAM, log, views and reservations and are unchanged by replacing
the device field.

`read_uart` and `read_plic` derive equalities with the actual state from the
corresponding authority and client half, reversing the source agreement
orientation explicitly. `write_uart` and `write_plic` combine both halves
through the checked native update and return the new client half alongside
all seven era conjuncts. The other two devices, durable disk, RAM and
registers are framed. No unowned device field is synthesized.

The four concrete fixed-state adapters use the existing generation
certificate and active-era agreement. They discharge `DeviceSpec` with its
proved implementation. Their use of `live_update` is justified by exact
definitional preservation of generation, power and durable disk. The
independently importable specification and registry link introduce no new
slots or runtime names.

The UART update is deliberately a **powerInterp** resource update. An
arbitrary UART replacement can change its wire history, so it would not by
itself preserve the observation conjunct of the full state interpretation.
The current theorem makes no such claim. A subsequent UART/MMIO WP must
also prove the actual transition's observation coupling or supply the
corresponding observed-step resource update. Likewise these theorems do
not justify arbitrary durable-disk mutation.

Independently reran `python3 tools/lake.py build
MachCSL.Logic.EraDevicesLink`: 414 jobs passed. The separate namespace and
adapter audit `/tmp/xv6-lean-research/EraDevicesIndependentAudit.lean`
checks complete dependency cones against the `propext`, `Classical.choice`,
`Quot.sound` allowlist. Output is in `era-devices-independent-axioms.log`.
No correction was required.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
