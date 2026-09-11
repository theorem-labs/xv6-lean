# mycpu register-sequence bookkeeping

Frozen Defs/Spec/Proofs/Link, source ProofMycpu.v:73–95,250–318.
The expressions reuse the actual Scalar.after, Memory.after and Return.after
post-states. `pushed`, `framed`, `computed`, `restored`, `popped`, `returned`
record the eleven GPR updates and final return-target update. The AUIPC PC
is explicitly supplied at its checked instruction address. The two load
post-states use the entry RA and S0 as their word arguments.

This is pure bookkeeping for later instruction-rule composition: it does
not prove that fetch established that PC or that memory returned those
saved values. Those require the actual cycle and native stack resources.
No alternate machine semantics or whole-function execution claim is made.

`push_sp`, `framed_sp`, `computed_sp`, `popped_sp` prove modular SP geometry.
`saved_sp`, `saved_s0`, `saved_ra`, `abi` prove restoration including all
thirteen source callee-saved registers. `computed_result` and `result`
yield the full modular mycpuRet expression for arbitrary TP. `return_address`
preserves the real JR low-bit clearing. The public Spec is constructed.

Build: `python3 tools/lake.py build Xv6.Kernel.MycpuRegisterSequenceLink`
passed 525 jobs. Owner full physical audit checked 55 logical declarations
in four modules, including opaque values, types and constructor dependencies;
standard three axioms only, no exclusions or unsafe/partial logical cone.
An initial spelling error in a BitVec rewrite failed compilation and was
corrected before this successful build. No generated file or dependency
was changed. Evidence: /tmp/xv6-lean-research/mycpu-register-sequence-
{build,audit}.log and MycpuRegisterSequenceOwnerAudit.lean.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
