# Native supervisor translation from the source residue

Complete for the approved full `translateAddr` boundary. The six pure, three resource and one native specification fields have implementations. `nativeSpec` supplies all component rules internally; `registrySpec` uses the unchanged 48-slot registry. The six modules are `KptAddressDefs`, `KptAddressSpec`, `KptAddressGeometry`, `KptAddressResources`, `KptAddressProofs`, and `KptAddressLink`. Approved Defs/Spec signatures are unchanged.

Source correspondence is `KptShare.v:320–482` (`tlb_res_pt_translateAddr_at`) and the per-event `HartSKpt.v` shared translation proof, at pinned artifact `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The actual generated operation is `Sv39Address.program`, defined as `translateAddr (.Virtaddr address) access`; the proof composes the real outer prefix and suffix with `KptTranslate.program` (`translate 39`).

The caller supplies exactly five fractional register cells: mstatus, current privilege, PMA regions, HTIF and MENVCFG. Source `KptResidue.residue` supplies the four full cells for SATP, TLB, PMP configuration and PMP addresses, plus exact SATP facts, coherent snapshot, PMP facts, shared invariant and publication credential. `open_residue` extracts those actual values; `partition` assembles the exact nine distinct owned registers used by the three-cell outer and six-cell inner rules. There is no duplicate ownership, fraction upgrade or new register authority.

The proof-side `prepare` overlay combines only the four owned residue values with the caller's partial description. `tor_of_vectors` transfers all six source TOR facts from the actual owned vectors. It does not infer facts about unowned caller PMP values or assert that an unrelated complete register file is the actual machine state. The native register rules subsequently check these owned cells against actual machine authority during execution.

For canonical addresses, `KptHardware.nativeSpec.mapped` opens and closes the shared invariant at the full native mask and derives the snapshot root, two raw pointers, leaf class and all address-specific hardware configurations. Then the actual outer register prefix, native TLB lookup/hit/miss/A-D programs and real success/error suffix execute. No Maps, Coherent, Canonical, successful lookup, current leaf word, address configuration, translation-body WP or restoration callback is an input to the public native rule. The returned path and branch facts are consequences supplied to the continuation.

For noncanonical addresses, the actual outer checked path returns its access-specific page fault. Canonical disabled-A/D errors pass through the real translation exception callback. Successful results preserve all 44 PPN bits and the 12 virtual offset bits before extension to the actual physical-address carrier. No error is replaced by an assumed success.

The postcondition returns the same five auxiliary cells and an exposed residue with exactly the original SATP and both original PMP vectors. Only its TLB field may change, with coherent snapshot ownership rebuilt from the actual branch. `preserved` proves the three unchanged fields, while `resources_close` explicitly recovers the standard source residue from that stronger named-value postcondition. Reservations and receipts retain the exact inner behavior, including exclusive reread reservations and conditional-write log receipts.

The guarded continuation preserves all canonical hit and miss alternatives. Noncanonical completion has no exposed memory-event guard; hit branches have zero/zero/one/two, and misses have three walk guards followed by those branch guards. Actual observed words, lookup selection and A/D facts remain inside their event guards. Register events still execute through the native fold. Guard counts are not claims about total machine-step counts.

The supported access family remains fetch, ordinary data load/store, and AMOSWAP with arbitrary acquire/release annotations, subject to the mapped permission and actual effective-privilege condition. Ambient configuration is explicitly Supervisor, SXL=2, the concrete `pmaBoot` list, and disabled HTIF on the caller's owned cells. The source's more general PMA predicate is not claimed here. MENVCFG remains the owned actual value, so both enabled and disabled A/D behavior are retained.

This layer neither allocates a concrete kernel page table nor proves the source supervisor/tier capability, cold-boot supervisor configuration, data-access wrapper or translated kernel function. It introduces no new ghost capacity or runtime name and leaves those subsequent composition tasks explicit.

Validation: `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.KptAddressLink` passed (990 jobs). Geometry compiled in 1.3 seconds, resource proofs in 1.1 seconds, the native proof in 1.6 seconds and the link in 1.1 seconds. All 230 physical declarations and their complete type, opaque-body (`allowOpaque := true`) and constructor cones passed the audit with zero exclusions, only `propext`, `Classical.choice` and `Quot.sound`, and no unsafe or partial dependencies. Audit evidence is `/tmp/xv6-lean-research/KptAddressOwnerAudit.lean`, with `kpt-address-owner-build.log` and `kpt-address-owner-audit.log` in the same directory. No existing component, generated source or umbrella was edited.

Independent coordinator review passes all six modules and a fresh full audit
of all 230 declarations. See docs/reviews/kpt-address-peer-review.md.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
