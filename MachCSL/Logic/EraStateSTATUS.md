# Register updates through the complete machine interpretation

`EraState.registers_access` extracts the global dependent register authority
and returns a wand restoring the complete era with arbitrary replacement
register files. The heap, devices, disk, timestamps, views, log, image and
reservation assertions are framed. Pure definitional equalities establish
that their predicates do not depend on register files.

`read_register` uses an arbitrary fraction of the typed register fragment to
read the actual state's value. `write_register` requires the full old fragment
and returns the full new fragment together with the updated complete era.
These proofs import the independently stated GlobalRegisterSpec only.
`writeBack_register` equates the actual hart-local/global write-back operation
to the new state definition, preserving all other harts and fields.

`MachineInterp.live_update` selects the exact registered current era and lifts
a proved update with an explicit client resource. It requires preservation of
generation, power and the actual durable disk; disk-changing steps cannot use
this rule. The concrete `power_read_register` and `power_write_register` laws
supply the proved register implementation and have no component-spec premise.

Build: `python3 tools/lake.py build MachCSL.Logic.EraStateLink` passes
(410 jobs). These are ownership updates and successor equalities; native
read/write instruction WPs are implemented separately in RegisterWP. General
memory/device/TSO instruction preservation remains open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
