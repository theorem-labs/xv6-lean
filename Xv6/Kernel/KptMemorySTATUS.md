# Shared-KPT ordinary virtual memory

Complete for the approved ordinary eight-byte virtual load/store boundary. All nine `PureSpec` fields and both `Spec` fields are constructed. `nativeSpec` and `registrySpec` supply actual native proofs with no component implementation or body-WP premise. The eight modules are `Defs`, `Spec`, `Pure`, `Plan`, `DataPlan`, `DataProofs`, `Proofs`, and `Link`. Approved Defs/Spec signatures are unchanged.

The actual programs are `vmem_read_addr`/`vmem_write_addr` and the optional actual `transform_effective_address` prefix at the already computed effective virtual address. The caller owns five auxiliary fractional cells and the source KPT residue. Its full SATP, TLB and two PMP vectors produce the exact nine-cell footprint, reused through every register prefix and data event. The input is the existing tier-indexed virtual context word; stores require the full fraction. Neither a physical word, translation-success fact, access callback, supplied per-address configuration nor trap-handler WP is a public premise.

The actual wrapper factors retain all translation, physical data and announcement errors with their exact `memory_exception` callbacks and offset fault addresses. False write-value results remain false. `completed` derives successful translation from actual native outcome facts, positive virtual-word canonicality and owned ADUE=1. Cached and physical A/D bits remain arbitrary and independent. The native data rules derive ordinary successful access from full context/word and actual physical hardware resources, including all permitted read views and own-author forwarding. No pristine-byte condition is added.

Translation hit guards (zero/zero/one/two A/D events) or miss guards (three walk events followed by those A/D events) precede exactly one ordinary data-event guard. Unknown read values and all branch facts stay inside their guards. The noncanonical and disabled-A/D alternatives are eliminated from native facts, while their exact raw program branches remain proved. Ordinary loads preserve the reservation after translation, which may differ from the incoming reservation because of a PTE reread; ordinary successful stores clear it. The store data event preserves the post-translation view, not necessarily the initial view. All translation receipts and the data event's view receipt are returned.

`KernelDatumWord.nativeSpec` exposes a physical word and a value-polymorphic closing wand from the virtual word. Its actual claims provide the physical RAM facts and mapping. The proof frames that ownership through translation and closes it after the data event, returning the original word on reads and the new word on stores. The complete source KPT residue is reassembled, with its actual coherent post-TLB and unchanged other control cells. Full heap metadata, TSO updates, reservations, blocked retry and other machine bookkeeping are paid by the existing native event rules.

The source mapping, explicit ambient configuration and scope are in `docs/design/kpt-memory-boundary.md`. This is not a fetched instruction, supervisor capability allocator, interrupt/migration proof, concrete page-table allocation or complete translated `mycpu` function. It introduces no ghost slot or runtime name and changes no frozen component, generated source or root umbrella.

Validation: `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.KptMemoryLink` passed (1,013 jobs; final composition 1.4 seconds, Link 902 ms). Fresh audit checked all 201 physical declarations from the eight modules and their complete types, opaque bodies (`allowOpaque := true`) and constructors. Only `propext`, `Classical.choice` and `Quot.sound` occur; there are no unsafe/partial dependencies and zero exclusions. Evidence: `/tmp/xv6-lean-research/KptMemoryAudit.lean`, `kpt-memory-audit.log`, `kpt-memory-build.log`. Final hashes are recorded in `kpt-memory-frozen.sha256` in the same research directory.

Complete independent coordinator review passed after reading all eight
modules and a fresh full 201-declaration audit; see
docs/reviews/kpt-memory-peer-review.md.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
