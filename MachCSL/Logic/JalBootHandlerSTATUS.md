# Eleven-thread JAL boot handler

`harts_wp` applies the universal native JAL loop to all eight actual boot register
files. `boot_handler` splits the boot allocator's six resource bundles, installs
the UART, PLIC and PLIC-wire invariants, and proves the exact `powerFork` list:
eight harts, UART, reset disk, and PLIC. The handler quantifies over every actual
BootFacts witness and every freshly allocated era. The four code bytes are shared
at positive one-eighth fractions. The disk worker owns the actual reset device.

The read-only JAL client can discard unused boot resources affinely; the resource
partition helpers preserve them before that client decision. UART and power share
one observation invariant. Namespace separation between observations and UART is
an explicit checked namespace field. `registry_boot_handler` discharges every
callee contract with concrete native proofs at the shared 23-slot registry and
uses the InvGS supplied by its caller, without allocating another native world.

Validation: `python3 tools/lake.py build MachCSL.Logic.JalBootHandlerLink` passed
509 jobs. Independent review passed with a physical-origin audit of 25 declarations
and their complete logical cones, using only the three standard foundational axioms
and no unsafe/partial dependency or runtime companion exclusions. The closed
operational adequacy specialization is a separate integration step. This component does not claim xv6 verification.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
