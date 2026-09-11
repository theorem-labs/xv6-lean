# Native supervisor configuration component

The new Xv6/Kernel/SconfDefs/Spec checkpoint ports source IntrDefs.v595–686,
including the exact sconf_at accessor. Constants are the actual MIE_S=0x220
and MENVCFG_S=0xA000000000000000 from RiscvFetchExec.v225/240. The source
minstret_inv is emp (MinstretInv.v341); it contributes no counter ownership.
All references are at pin fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

Capacity is exactly MycpuRegimeShell.Capacity: its shared translation
capacity supplies the actual HardwareConfig and register cameras, and its
one bits capacity supplies the existing SupervisorBits.msOwnAt. There is no
new camera, no independently chosen duplicate register/bit capacity and no
translation invariant hidden in sconf.

The body retains hardware config, emp retirement marker, full Supervisor
privilege cell, existential msOwnAt, full mie/mideleg and full menvcfg. The
mie value is the pinned source constant; mideleg remains arbitrary subject
to mie & ~mideleg=0. MENVCFG retains all four source facts (PBMTE0,
PMM_Disabled, LPEfalse, FIOMnot1) and equality to the exact source literal.
The existing msOwnAt carries the full mstatus cell, SIE half and both sret
halves plus all ten SIE-agnostic mstatus facts. It does not fix SIE itself.
The hardware component includes the source static mapping claims and actual
generation certificate; its existing constructor must be paid with real
register ownership, not a synthetic symbolic file.

The source mstatus accessor is represented literally by msOwnAt(ms) *
(forall replacement, msOwnAt(replacement) -* sconf). It stores one resource
and a closer, never a second copy of the body. Its open/close laws preserve
all other exact ownership and accept any replacement that provides the
whole actual native triple and fact set. Additional bounded laws expose
hardware persistently, borrow interrupt-mask/environment cells with exact
reassembly, and derive typed register/SIE/sret agreements from real resources.

The checkpoint contains three pure facts and fourteen resource contracts.
All contracts now compile in893 jobs, with actual native
SupervisorBits/Registers proofs and BI framing. Hardware persistence follows
from its exact native definition, including the static claims and generation
certificate. The strict63-declaration full type/opaque/constructor audit passes
with zero exclusions; see SconfSTATUS.md. Independent final review remains
separate. It claims no boot construction, CSR operation, enabled
interrupt handler, full supervisor capability, or complete function adapter.
Hart-state, PC/counter ownership, translation residue/one-shot slot, stack,
GPRs and timer capability remain separately owned as in the source.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
