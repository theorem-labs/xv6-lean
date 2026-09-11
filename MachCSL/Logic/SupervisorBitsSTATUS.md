# Supervisor bit resource layer

All five modules (Defs, Spec, Proofs, Registry, Link) are frozen. `actual`
constructs all twelve independently stated native resource laws, and
`nativeSpec` instantiates them at the explicit registry. This is the
source bit/mstatus component; no full sconf, enabled interrupt arm, CSR
execution or installed-handler theorem is claimed.

Definitions match `IntrDefs.v:196–207,309–452,649–653,751,932–936` at
xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. They use native
`GhostVarG (BitVec 1)` and the existing typed register camera. All ten
SIE-agnostic mstatus facts are present, including the exact nominal-MPP
helper. `msOwn` owns the full actual mstatus cell, the SIE half tied to
its value, both tied SRET halves, and those facts.

Source mapping and proofs:

- `split`, `agree`, `allocate`, `flip`, `flip_four` preserve the native
  fractional ghost semantics. SIE fractions are half + eighth + eighth +
  quarter; the latter quarter is not by itself a handler credential.
- `sret_agree`, `sret_update`, `tie_congr` use separate SPP/SPIE names and
  two halves each. Changing their ghost value requires both halves.
- `attach` takes the existing full mstatus cell and its facts, allocates
  three fresh names, and returns `msOwn` plus every complementary fragment:
  both SIE eighths, the quarter and both traveling SRET halves. It neither
  rewrites the physical register nor allocates another register authority.
- `live_bit`, `off` derive the bit from the live tie and the arm eighth;
  `count_index` proves the source depth/base-enable relation. These pure
  consumers can be used through proof-mode pure elimination when the caller
  needs to retain the input resources; their conclusions do not themselves
  contain replacement ownership.

Registry slot 44 extends FsCrash slots 0–43. `registry_old` preserves all
previous slots and `registry_unused` preserves 45 onward. Every existing
FsCrash capacity is reconstructed at its original slot, including the
complete machine/heap/durable-disk resources. `physical_registers_same`
checks the bit layer uses exactly the machine's register capacity.
SIE/SPP/SPIE all share this one camera at their existing Era name fields.
No boot allocation is claimed merely from those canonical names; attachment
returns existential fresh names, and installing them into a new era remains
an explicit generation-aware integration obligation.

No mutable bit is converted to discarded ownership. Ghost flips retain all
pieces and are not instruction-execution theorems. The resource named
`armBit` is only the ghost eighth, so its true case does not falsely assert
that a handler or migration contract has been installed. HartTp, full
sconf, translation/tier, timer and handler integration remain in
`docs/design/supervisor-capabilities-boundary.md`.

Validation: `python3 tools/lake.py build MachCSL.Logic.SupervisorBitsLink`
passed 578 jobs (Proofs 1.0s, Registry 1.2s, Link 806ms). The fresh physical
module-origin audit checked all 234 declarations in all five modules,
including private helpers, types, opaque bodies with allowOpaque=true and
inductive constructors. Only propext, Classical.choice and Quot.sound occur;
no unsafe/partial logical dependency and zero exclusions. No custom axiom,
sorry, native_decide or bv_decide was introduced. Evidence:
`/tmp/xv6-lean-research/SupervisorBitsAudit.lean`,
`supervisor-bits-build.log`, `supervisor-bits-audit.log` and
`supervisor-bits-frozen.sha256`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
