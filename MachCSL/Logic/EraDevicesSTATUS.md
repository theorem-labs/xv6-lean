# Device updates through complete machine interpretations

EraDevicesDefs/Spec/Proofs/Link provide full device-authority access and
reconstruction through all seven era conjuncts. Reconstruction requires the
actual durable-disk contents to be unchanged, preserving both per-era disk
ownership and the fixed durable authority. Register, RAM, TSO and reservation
components are framed with definitional equalities.

Concrete UART and PLIC half agreement/update rules return the new client
fragment. Fixed-state wrappers identify the registered current era and retain
all power counters, registry and disk resources. The registry theorem supplies
concrete capacities; fixed wrappers supply the proved native DeviceSpec.
No successor oracle, new camera, or arbitrary disk mutation is assumed.

Validation: `python3 tools/lake.py build MachCSL.Logic.EraDevicesLink` passed
414 jobs. Independent review passed; see docs/reviews/era-devices-review.md. The reviewer checked all 25 declarations with only standard axioms. These are
ownership bridges for later UART/MMIO step rules, not device WPs themselves.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
