# KernelStack independent peer review

PASS for the declared virtual scratch-stack resource slice. Codex's artifact
audit agent independently read all four coordinator-authored
`Xv6/Kernel/KernelStack{Defs,Spec,Proofs,Link}.lean` modules, their status and
design, and all 645 lines of upstream `iris/StackOwn.v` at paper pin
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. No correction was requested.

The source mapping is `pa_stk` at line 45; `stack_own` at 151; zero,
append, split and one-slot laws at 155–214; two-slot elimination and
introduction at 283–304; SP bounds at 374; tier weakening at 477; and
nonzero SP at 522. The two-slot frame theorem composes these source laws.
The actual native `KernelDatum.word` retains the mapping claim, positive
canonicality, RAM and tier facts, and physical context byte/timestamp
resources. This dependency was inspected along with the previously reviewed
virtual-word bridge.

The carrier is the exact existential list of 64-bit contents, its length,
and the indexed separating conjunction at `sp - 8*(i+1)`. The reused
`StackPhysical.paStk` performs modular subtraction for arbitrary natural
depths. The split proof uses the original list's take/drop decomposition
and proves its lengths before shifting the deeper addresses. Joining uses
the supplied words; it neither duplicates the old contents nor allocates
replacement memory. The two-slot frame retains the entire deeper stack,
including its unchanged context and tier.

Tier weakening acts pointwise on the existing virtual words. The first
owned byte's positive-canonical address fact rules out subtraction
underflow and proves the exact source bound
`8 ≤ sp.toNat ∧ sp.toNat < 2^38 + 8`; nonzero follows. No global stack
layout or extra distinctness premise is introduced. All nine Spec fields
are discharged by native proofs, and the registry link supplies the actual
capacity without an external implementation premise.

Independent validation: building `Xv6.Kernel.KernelStackLink` together with
the separate timer signature checkpoint passed 666 jobs. A fresh audit
selected every declaration by physical origin in the four modules,
including private declarations: 38 declarations passed `collectAxioms`
with only `propext`, `Classical.choice` and `Quot.sound`. Recursive traversal
of types, opaque bodies (`allowOpaque := true`) and inductive constructors
found no unsafe or partial dependencies; zero declarations were excluded.
Evidence is `/tmp/xv6-lean-research/KernelStackPeerAudit.lean`,
`kernel-stack-peer-audit.log` and `kernel-stack-peer-build.log`.

The remaining source transport, context domination/reindexing, slot/base
enumerations, boot conversion and reclamation are explicitly outside this
slice. This proves resource algebra, not stack allocation, machine
execution or a complete function theorem.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
