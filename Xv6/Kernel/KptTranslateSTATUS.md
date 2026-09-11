# Shared kernel Sv39 lookup and translation

Complete for the approved `translate 39` boundary. All three `PureSpec` fields and the native `Spec.translate` field have implementations. `nativeSpec` discharges the full native hit and miss specifications; `registrySpec` instantiates the existing 48-slot registry. No camera or ghost name was added. The approved Defs/Spec signatures are unchanged.

The five modules are `KptTranslateDefs`, `KptTranslateSpec`, `KptTranslatePureProofs`, `KptTranslateProofs`, and `KptTranslateLink`.

Source correspondence uses `.upstream/xv6iris` at `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. `HartSKpt.v:1185–1294` dispatches the shared-table translation by matching entry, foreign hash collision, or empty slot. The actual Lean program is `LeanPaperStock/Vmem.lean:541–549`: one `lookup_TLB 39` followed by `translate_TLB_hit` or `translate_TLB_miss`. `program_factor` is a kernel equality retaining both alternatives and the real hit index. `lookup_plan` widens the proved actual one-read plan to the same six-cell footprint.

`lookup_resident` proves optional vector residency from the actual lookup. `lookup_mapped` uses coherent provenance and deterministic tree mapping to identify both raw upper pointers and the mapped leaf, then normalizes stale A/D bits. It proves the hit entry has the supplied mapping's PPN and permission. There is no assumed matching-entry result, injective hash, frozen physical leaf, or direct physical-slot resource.

`wp_dispatch` invokes the existing native hit or miss contract according to the actual lookup value. `wp_translate` folds the real TLB register read and then this dispatch. `resources_hit` restores the full bound/credential clients around the hit; `resources_miss` retains all three actual walk receipts. Both restore the same six owned register cells, exact branch reservation, shared snapshot clients, A/D receipt, and coherence of the successor TLB.

The continuation offers hit and miss alternatives with ordinary conjunction, without duplicating linear resources. Hit A/D branches retain zero/zero/one/two guards. Misses retain three leading walk guards before the leaf/view selection, followed by those A/D guards. Actual lookup-selection and A/D facts are introduced inside the guards. These are the exposed memory-event guards, not a claim that register reads consume no machine steps. All register events execute through the native partial-footprint fold.

The generic config is exactly `KptMiss.Config`: three walk regions plus the leaf A/D physical configuration. Access support and permission, mapped snapshot path and initial coherence remain explicit pure inputs. The program is fixed to Supervisor and Sv39, with arbitrary ASID and MXR/SUM arguments. Disabled A/D retains the actual `PTW_PTE_Needs_Update` error; other branches preserve actual hit-refresh/miss-fill successors and returned PPN/PBMT. The underlying shared event proofs retain blocked overlap and failed conditional-write behavior.

This does not yet prove `translateAddr`, SATP selection, canonical VA handling, effective privilege, concrete table initialization, or a translated kernel function. It does not derive the physical configuration from an ambient supervisor capability. The full source virtual-register/tier interface remains separate.

Validation: `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.KptTranslateLink` passed (849 jobs; native proof module 1.5 seconds, link 946 ms). The audit passed all 133 physical declarations and their full type/opaque/constructor cones, including private declarations, with zero exclusions; only `propext`, `Classical.choice` and `Quot.sound` occur, and no unsafe or partial dependency was found. Full audit evidence is `/tmp/xv6-lean-research/KptTranslateOwnerAudit.lean`, with build and audit logs `kpt-translate-owner-build.log` and `kpt-translate-owner-audit.log` in the same directory. No existing source, generated model, umbrella or other owner's module was edited.

Independent coordinator review passes all five modules and a fresh full audit
of all 133 declarations. See docs/reviews/kpt-translate-peer-review.md.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
