# Independent review of complete Bare mycpu composition

Verdict: PASS for the declared Bare physical-resource function-CPS scope.
This review was performed by the Codex `lean_logic_audit` subagent,
independently of the implementation's author. No correction was required.

I read all eight `Xv6/Kernel/MycpuBare{Defs,Spec,Geometry,State,Reference,Config,Proofs,Link}.lean`
modules, their STATUS and design, the complete pinned `SpecMycpu.v` and
`ProofMycpu.v`, and the immediate native MycpuCycle and CycleShell
composition proofs. Source pin: xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`; the relevant source interfaces
are `SpecMycpu.v:31` and `:58`, implemented at `ProofMycpu.v:59` and `:323`.
Actual instruction offsets and encodings were also checked against the
existing MycpuDecode definitions and their previously certified image
boundary.

## Actual execution and configuration

The public `Spec.function` and `Spec.hart` contracts require one entry
configuration and actual native resources. They accept no per-instruction
success, trace, configuration or clock-preservation premise. The private
chain invokes the actual native cycle rules for all fourteen instructions:
the stores at indices 1 and 2, loads at 10 and 11, return at 13, and the
nine scalar instructions. Its only remaining program obligation is the
ordinary next-cycle WP at the established return boundary.

Each cycle includes the existing checked fetch/decode, actual instruction
body, retirement, optional clock tick and restart. Both initial tick
choices and all subsequent tick choices remain quantified. Arbitrary
counter values, overflow, inhibit configuration, pending interrupts and
hardware pin values are not replaced with a fixed reset execution. The
single entry configuration explicitly provides Supervisor mode, disabled
SIE, delegation, source MISA/MENVCFG, relevant status fields, Bare SATP,
entry-zero TOR grant, actual board PMA and disabled HTIF. Configuration
lemmas derive every intermediate requirement from these facts and actual
cycle postconditions.

`Phase`, `CoreEq` and the structurally recursive `reference` are pure
register bookkeeping. The native proof first executes each cycle rule and
then uses its actual `Completed` consequence to recover the next phase.
It does not use the reference sequence as a memory or execution oracle.
The ignored counter/clock projection does not freeze physical hardware
pins or assert ownership of the whole register file. The true 2/4-byte
instruction widths are retained, including AUIPC at offset 14.

## Resources and result

The native footprint consists of 28 cells and an independent eleven-cell
callee-saved frame. The combined 39 keys are proved distinct; SP and S0
are already in the main bundle and are not duplicated. Fractions of
read-only and framed cells remain explicit. The code resource is the
discarded 34-byte fetch span, covering the 32-byte function and the fetch
boundary bytes.

Both modular stack addresses, entry SP minus 8 and minus 16, carry actual
full context-word resources. Their alignment and physical RAM membership
yield the required bounded PMA geometry; there is no added global stack
no-wrap or sixteen-byte alignment assumption. Prologue stores replace
the old scratch contents with entry RA and S0. Those same linear
byte/timestamp resources justify the later loads at every allowed view
and are returned with the saved values. Neither load result is a caller
premise.

The initial reservation is arbitrary. Actual restart clears it, so the
remaining cycle boundaries and final continuation receive `none`.
Fetch/data receipts are obtained and may be affinely discarded; the
proof does not infer an unjustified relation between their timestamps.
The public final continuation is unguarded, while the internal native
rules retain their own guards.

The result proves both PC and nextPC equal to the low-bit-cleared entry
RA, restores RA and all thirteen ABI callee-saved values, and computes
A0 from the arbitrary entry TP. The hart specialization explicitly assumes
TP equals the chosen CPU and derives `0x800123e8 + 128 * cpu.val`; it does
not claim allocation of the source HartTp invariant.

## Source scope and validation

This is a complete native NotStuck CPS proof of the Bare body, including
its return instruction. It does not implement the source's tier-polymorphic
SIE/sconf capability, virtual free-stack recombination, KPT translation or
the preceding JAL callable wrapper. It also does not establish termination,
a concrete execution witness or whole-kernel adequacy. These boundaries
are stated accurately in STATUS and the design. The optional arbitrary-n
physical-stack corollary remains explicitly unimplemented.

Independent `python3 tools/lake.py build Xv6.Kernel.MycpuBareLink` passed
721 jobs. A fresh physical-origin audit checked all 347 logical
declarations from the eight modules, including private declarations,
types, opaque bodies with `allowOpaque := true`, and inductive
constructors. Only `propext`, `Classical.choice` and `Quot.sound` occur.
The sole excluded runtime root was the exact declaration
`Xv6.Kernel.MycpuBare.reference._unsafe_rec`; the audit verified the
compiler naming relation and its safe structural-recursion parent. No
unsafe or partial declaration occurs in any logical dependency cone.
All eight frozen SHA256 checks passed after the review and validation.

Evidence outside the repository:
`/tmp/xv6-lean-research/MycpuBarePeerAudit.lean`,
`mycpu-bare-peer-audit.log`, `mycpu-bare-peer-build.log`, and
`mycpu-bare-frozen.sha256`. No owner code was changed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
