# Boot PMA producer: frozen native component

All five pure and eight native approved contracts are implemented in four
modules. Complete build: 872 jobs (Proofs 5.5 seconds, Link
1.1 seconds). Strict owner audit checked all 63 physical declarations,
including generated/private origins, with exporting disabled and complete
type, opaque-body (allowOpaque=true) and constructor traversal. Standard
three axioms only; no unsafe/partial dependency, zero exclusions. No sorry,
custom axiom, native_decide or bv_decide. nativeSpec and registrySpec have
no supplied component-law premises.

Source ArchReset.v:245–276 writes the board's PMA parameter before the real
generated initialization. Existing BootUniversal.bootFacts_static proves
the actual pmaBoot result for every BootFacts hart, including arbitrary
preboot register files. Source pin: fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.

partition_hart applies native finite-map deletion to initialMap, retaining
the exact dependent payload at every other generated register key.
Ordinary kernel decide checks the filtered enumeration has 179 distinct
keys; the general lookup and membership theorems identify exactly those
keys. partition_all splits the actual complete Fin 8 separating conjunction.
persist_all consumes each full PMA fragment through native register
persistence. The resulting individual cells and complete bundle are
persistent. No full PMA fragment or full-cell restoration wand is returned.

produce preserves every TSO byte, timestamp and log-length client, every
heap metadata token, device fragment, durable-disk client and reservation.
produce_text_retained consumes only the register column already retained
by KernelTextBoot. Its exact sparse byte/timestamp deletion remainder and
all metadata—including metadata at carved text keys—remain owned.
produce_text composes the two native updates, with whole-result updates
explicitly parenthesized in the public contracts.

allocate_text calls the actual KernelTextBoot.allocate once. It returns
the real boot era interpretation, image equality and AuxiliarySame,
persistent physical text, all eight discarded PMA cells, and every
remaining client. encodeAll is only a symbolic witness. This establishes
no source supervisor capability, physical KPT, translation resource or
complete native function-entry state. No registry slot, previous owner
file, generated semantics or umbrella was modified.

Reproduction:

- PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.BootPmaLink
- PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/BootPmaOwnerAudit.lean

Evidence: /tmp/xv6-lean-research/boot-pma-{build,owner-audit}.log and
boot-pma-frozen.json. Design: docs/design/boot-pma-boundary.md. Independent coordinator review passed all four modules and a fresh
63-declaration strict audit; see docs/reviews/boot-pma-peer-review.md.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
