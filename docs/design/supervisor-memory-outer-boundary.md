# Effective privilege and outer supervisor memory access

Root-owned next prefix: SupervisorMemOuter{Defs,Spec,Plan,Proofs,Link}+STATUS.
Read the actual generated Mem.lean:460–530,586–613, SysControl.effectivePrivilege,
the existing source-shaped SupervisorBare effective-privilege proof, and the
native checked read/write interfaces. The bounded result wraps those complete
native checked eight-byte rules with the actual outer effective-privilege reads
and metadata/callback handling; address translation and instruction bodies
remain separate.

Own two independently fractional cells, mstatus and current privilege, in
addition to the four already supplied physical permission cells. The actual
prefix reads mstatus then current privilege and returns Supervisor when the
actual privilege is Supervisor and MPRV is clear. A generic prefix theorem
also supports InstructionFetch without an MPRV restriction, exactly as the
generated effectivePrivilege definition does. Other status bits, including
MPP and SXL, remain arbitrary at this API. No reset or complete sconf snapshot
is required.

Prove equality of the actual explicit-privilege read callback/metadata wrapper
with checked_mem_read followed by the actual drop-meta function; preserve
both success and error values. Use the already checked ordinary-write callback
equality. Factor actual mem_read/mem_write_value through the two-read prefix.
Native public read/write WPs construct this prefix themselves, then invoke
SupervisorRead/SupervisorWrite with the actual source facts and context word.
They return both privilege cells, the physical cells and the complete native
context/read or write resources, including the correct receipt and reservation
behavior, through the real guarded memory continuation. No physical-WP oracle
or state preservation callback is a public input.

A further register-only mem_write_ea rule is useful in this same owned prefix
if its exact singleton-loop PMP staging builds independently: it has the same
two effective-privilege reads, PMA once and PMP cfg/cfg/address, followed by the
actual pure write_ram_ea announcement. It performs no MMIO check or writeMem
event itself. This optional stage must not be silently omitted from later
vmem_write/instruction composition. It requires exact width-eight alignment,
PMA match/writable and TOR/RAM facts, not word-result ownership.

The frozen prior prefixes and generated sources stay unchanged. No new camera
is needed. Audit every added physical declaration with types, opaque bodies and
constructors and standard three axioms. This leaves virtual address formation,
canonicality, Bare/KPT translation, checked instruction fetch and full function
composition open; those are not assumptions disguised as proved interfaces.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
