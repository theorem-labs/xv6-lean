# Actual boot clients to persistent sparse kernel text

KernelTextBoot now implements the unchanged approved ten pure and four
native resource contracts in six modules:868 jobs pass. All94 physical
declarations passed the full type/opaque/constructor audit, standard three
axioms only, zero exclusions. Final coordinator review is pending. It consumes the actual Era.bootClients for pinned xv6
BootFacts and produces KernelTextImage.physicalText, without a physical-text
input, static-map assumption or translation/execution premise.

Source read: BootCarve.v header and complete relevant sections1–5
(boot_raw_bytes/sub_text, static-claim persistence, raw-byte split,
boot_text_persist and kernel_text_intro), plus the full text-ledger carve
and persistence section at1190–1270. Also read native BootWindow's complete
extract_words dependency, MycpuBootResources definitions/specification/
extraction/sharing/allocation, KernelTextImage's sparse representation and
its pure proofs, and the actual imported code/ELF correspondence. Pin:
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

The source's full sub-etext partition is broader than the named sparse
kernel_text map. This producer selects exactly the latter, leaving holes
owned in its explicit remainder. There are seven descriptors, in original
source order: five4096-byte runs, a2976-byte run and a292-byte run. Together
they are23748 bytes, with physical domains
[0x80000000,0x80005ba0) and [0x80006000,0x80006124). The source comment's
older23340 count is not used. No default-valued code byte fills an absent key.

Each descriptor uses the actual ByteRun base/length/payload and a finite
BitVec of exactly8*length bits. The pure bytes contract proves the integer
shift/modulo byte bridge; descriptor payload evaluation is not an oracle.
The pure unique/domain/count contracts identify exactly the selected sparse
physical keys, with no modular-address collisions or duplicate spending.
The actual sourceMap successful lookup is tied to loadedRam via existing
Kernel.code_loaded/ELF slice certificates and the actual boot loader. Every
BootFacts memory therefore supplies the selected byte. FiniteMap.decode
memory=g.memory is the explicit representation link to that same state,
not an independent memory-image assumption. Timestamp zero follows from
the actual bootTimestamps map at the same successfully present keys.

extract uses one BootWindow.extract_words application with all seven
words, full byte clients and full timestamp clients. It returns rawText
plus retained. The latter includes both literal deleteKeys maps, the actual
log-length lower bound0, all180-register-per-hart clients, all metadata
tokens (including selected text keys), all device and durable-disk clients,
and all reservation fragments. The polymorphic outside contract exposes
that every unselected byte and timestamp lookup is exactly unchanged.
No client is reallocated during extraction.

persist consumes the extracted existing timestamp fragments by the native
persistence update, producing discarded timestamp-zero receipts. It also
persists the existing raw byte fragments and assembles the successful-lookup
physicalText predicate from the seven persistent run windows. This matches
the source boot_led_text_persist resource discipline: the element was paid
by era initialization, not freely minted above the state interpretation.
It introduces no context, tier claim, static authority or physical tree.

The approved produce signature returns `(bupd physicalText) ∗ retained`,
so retained is available beside the pending text update. The explicit
produce_update corollary uses native bupd_frame_right to return
`bupd (physicalText ∗ retained)`. allocate uses that combined update and
discharges its own boot/representation premises:
use actual Xv6.Machine.boot before and symbolically use
FiniteMap.encodeAll g.memory, whose decoding theorem supplies equality.
Native Era.allocate creates the actual state interpretation and clients;
produce consumes those clients. The output retains Era.interp, the exact
image equality, AuxiliarySame with the caller's template, physicalText and
all retained clients. The64-bit exhaustive witness is never executed.
Template auxiliary names remain caller-provided names; no associated
kernel camera authority or installation is manufactured.

Root KernelTextImage.physical may later combine physicalText with actual
static claims to produce identity text. That is intentionally a separate
step and does not install the static ghost map or a physical KPT. This
producer likewise does not establish supervisor registers, a boot handler,
native function preconditions, code execution or the paper's adequacy root.

Implementation remains within KernelTextBoot: PureProofs, Proofs, Sharing
and Link, plus STATUS. No generated map, existing extraction theorem,
other-owner prefix or umbrella was changed.

Validation: PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build
Xv6.Kernel.KernelTextBootSpec. Log:
/tmp/xv6-lean-research/kernel-text-boot-signatures.log.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
