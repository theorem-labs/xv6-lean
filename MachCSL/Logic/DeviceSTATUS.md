# Device ownership bridge

`DeviceDefs/Spec/Proofs/Registry/Link.lean` port the six device bridge laws from
`iris/RiscvPtsto.v:1914–1968` at the paper pin. The assertions use native Iris
`GhostVarG` at the actual `Uart.State`, `Plic.State`, and `Virtio.State` types.
For each device, the machine interpretation and client fragment own one half.
Agreement consumes both halves to establish equal state; their joint update can
change the value. No update from one half alone is provided.

`interp` is the separating conjunction of the three machine halves.
`fragments` is the corresponding client bundle. `alloc` allocates three ghost
variables and splits each into halves; `agree` and `update` compose the individual
laws. The three `interp_*_update` rules frame the untouched devices. These are
ownership rules; their target states must still be tied to actual machine steps
by the future lifting rules. In particular, arbitrary ghost updates are not
claims that arbitrary hardware transitions exist.

Capacity and runtime names are separate. The combined registry extends the
register/TSO registry with UART at slot7, PLIC at8, and Virtio at9. Preservation
theorems cover every old slot and every unused slot. Explicit capacities retain
the register, history, view, and byte/timestamp resources at their original slots.
The client contract is defined independently of its implementation and linked by
`registryDeviceSpec`. Device initialization allocates ownership of the supplied
state; it neither resets a disk nor presumes the initial fs.img on reboot.

Validation: `python3 tools/lake.py build MachCSL.Logic.DeviceLink` passed.
The ownership modules compile in about one second each. A separate audit driver
checks all namespace declarations, including definitions and private helpers,
against `propext`, `Classical.choice`, and `Quot.sound`. Whole-machine state
interpretation, power-era resources, lifting, and adequacy remain unimplemented.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
