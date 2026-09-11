# Independent MycpuBareWitness review

PASS for the stated operational-witness scope. I am the Codex
`lean_logic_audit` peer reviewer, separate from the witness implementer. I
read all nine implementation modules, their STATUS/design, the relevant
existing MycpuBare state/result machinery, pauseRun soundness, actual
NodeStep/cycle and pool lifting, and the pinned source instruction/result
contracts. No implementation correction is requested; I changed no witness
code.

The performance refactor preserves full state equality. OrderProofs proves
CoreEq generically for the 173 registers outside the exact seven-element
list PC, nextPC, minstret_increment, minstret, mcycle, mtime, mip. Each of
the fourteen certificates separately checks all seven excluded fields and
uses function extensionality to recover equality of the entire typed
180-register file. Its first equation still reduces `run 4 (cycle false)`
on the actual generated program; the compact bodyFile/reference is an
expected result, never a replacement interpreter or supplied instruction
success premise. Each certificate also compares the complete local state,
including memory, devices, log, view, and reservation.

The bounded evaluator is sound for every accepted input. pauseRun preserves
an unsupported event and its continuation without stepping it. The outer
run accepts only an ordinary RAM write with a present payload; all other
unsupported events or exhausted fuel fail. run_sound proves the real write
NodeStep with the exact request and retained continuation, actual writeBytes,
full snapshot append authored by hart 3, unchanged ordinary view and cleared
reservation. The empty other-reservation set is discharged by the concrete
global state, not assumed for arbitrary machine executions. Each ordinary
read uses the actual Memory.read at the current permitted view. Thus the
two restores can observe this hart's own stores above view zero through the
real TSO read definition.

The read cache is proved equal as a total map to loadedRam bootImage. Its
34 code bytes are tied to the imported kernel image, including the last
fetch's two-byte spill beyond the 32-byte function body. The specialized
zero interval is justified by bootByte_after_file and the remaining cases
retain the real image. This is not an unchecked replacement image or read
oracle. Source instruction correspondence is the complete CodeMycpu.v
fourteen-instruction sequence; the SP save/restore and result arithmetic
match ProofMycpu.v and ProcGeom.v. Source pin is
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; the generated model remains pinned
at `23dcf8fd923eb8a1958795393d2975632aa940b2`.

Cycles composes fourteen complete generated cycles with an actual restart
transition before each one. Choosing optional tick=false is a permitted
existential schedule. It does not change the transition relation or the
previous native WP's universal clock behavior. Pool lifting uses the actual
live-hart primitive and fixed occurrence, preserving other harts and devices;
it does not turn an instruction into an atomic machine step. pool_positive
rules out the zero-step run using distinct initial/final PCs.

The final actual theorem constructs all eight Spec fields: concrete
EntryConfig, total cache equality, fourteen cycles, NodeSteps, MycpuBare.Result,
exact result and stack values/two-message log, preservation of all 34 code
bytes, and real PoolSteps. Additional theorems establish positive step count,
initial/final MemoryOK and ReservationsOK, exact global frames, and HartResult.
CPU3 returns A0=0x80012568; RA/S0/SP are restored; minstret=14; mcycle/mtime/view
remain zero and no reservation remains.

This establishes operational inhabitation from the explicitly configured
powered-on supervisor state. Boot reachability of that state and allocation
of its native Iris entry/context/stack resources are still open. The
singleton fixed-hart schedule also does not establish arbitrary-interleaving
safety, shared-KPT translation, enabled-interrupt handling, or a complete
source mycpu theorem. The existing general MycpuBare WP is separate and
unchanged. The witness documentation makes these limits explicit.

Independent validation passed: the target build completed 733 jobs, and a
fresh physical-origin audit checked all 165 logical declarations in all
nine modules, including private helpers, types, opaque theorem bodies and
datatype constructors. Only propext, Classical.choice and Quot.sound occur.
The sole excluded root is compiler-generated run._unsafe_rec, checked against
its safe total source owner; it is absent from every logical dependency
cone. No unsafe/partial declaration occurs in those cones. The review
also checked that no initial-allocation dependency was imported into the
witness proof cone. All nine source SHA256 hashes stayed unchanged during
the build and audit.

Local evidence: MycpuBareWitnessPeerAudit.lean,
mycpu-bare-witness-peer-build.log, mycpu-bare-witness-peer-audit.log and
mycpu-bare-witness-peer-before.sha256 under /tmp/xv6-lean-research.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
