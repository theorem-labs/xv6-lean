# Sparse kernel-text boot producer: frozen native component

All ten pure and four native approved contracts are implemented in six
modules. Full build868 jobs (PureProofs1.4s, Proofs1.0s, Sharing1.2s,
Link1.1s). Strict owner audit checked all94 physical declarations, including
private/generated origins, with exporting disabled and full types/opaque
bodies (allowOpaque=true)/constructors. Standard three axioms only; no
unsafe/partial dependency and zero exclusions. No sorry/custom axiom,
native_decide or bv_decide. Generic nativeSpec and the existing48-slot
registrySpec have no supplied component-law premises.

Sources: BootCarve.v sections1–5, particularly boot_bytes_split,
boot_text_persist and kernel_text_intro; the full text-ledger carve and
boot_led_text_persist at1190–1270; actual KernelInstrs.v imported code map,
KernelMapsCertificates and parsed ELF correspondence. Pin:
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

This is an exact sparse named-text carve, not the entire sub-etext split.
Seven descriptors retain original source order and payloads: five4096-byte
runs plus2976 and292, exactly23748 distinct physical keys. The holes below
etext remain owned in the exact remainder. No default byte is introduced.
The source's stale23340-byte comment does not determine the actual count.

PureProofs checks each actual payload fits its explicit descriptor width,
then proves every byte's shift/modulo representation. Ordered disjoint
intervals plus modular-address bounds establish key uniqueness without
quadratic comparison of all23748 keys. domain identifies exactly successful
sparse source lookups. Existing source→actual loaded ELF certificates and
the actual boot loader establish each loadedRam byte; actual BootFacts and
finite-map decoding transfer it to client-map lookup. Timestamp zero comes
from the real bootTimestamps map at those same present keys. The generic
outside theorem proves every unselected byte/timestamp lookup unchanged.

extract_initial invokes BootWindow.extract_words once on all seven runs.
extract consumes the actual Era.bootClients and retains literal deleteKeys
byte and timestamp maps, the actual log-length0 receipt, all register-file
clients, all metadata tokens including selected text addresses, all device
and durable-disk clients and all reservation fragments. No second allocator
or free timestamp mint occurs.

persist_word consumes the existing full timestamp fragment through native
persistence and separately persists its real byte fragment. physical_text
assembles the exact successful-lookup predicate from persistent run windows.
This produces KernelTextImage.physicalText only: no static map, tier claim,
translation, register configuration or physical page table is installed.

The approved produce signature is deliberately preserved exactly as parsed:
`clients ⊢ (bupd physicalText) ∗ retained`. The stronger separated output
makes retained available alongside the pending update. The explicitly
parenthesized produce_update corollary applies native bupd_frame_right to
obtain `clients ⊢ bupd (physicalText ∗ retained)`. The allocator uses this
combined update; no ownership or premise was weakened.

allocate uses actual Xv6.Machine.boot before and native Era.allocate. The
FiniteMap.encodeAll witness is used symbolically through decode_encodeAll,
never enumerated over64-bit addresses. Its output retains the actual era
interpretation, exact era.image equality, AuxiliarySame with the caller's
template, physicalText and every retained client. Auxiliary names do not
claim associated kernel-camera authority or native boot-handler readiness.

Reproduction:

- PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.KernelTextBootLink
- PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/KernelTextBootOwnerAudit.lean

Evidence: /tmp/xv6-lean-research/kernel-text-boot-{build,owner-audit}.log;
exact file hashes in kernel-text-boot-frozen.json. Final coordinator review
is pending. See docs/design/kernel-text-boot-boundary.md.

Static claim allocation and physical KPT installation, supervisor capability
initialization, native whole-function resource inhabitation and paper
adequacy roots remain separate. No existing owner file, generated artifact,
registry slot or umbrella was modified.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
