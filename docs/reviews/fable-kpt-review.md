# Fable ninth review: native shared Sv39 translation and publication

The review below is the unchanged result text returned by Claude Fable 5.1
through Claude Code, requested model `claude-fable-5-1` at max effort.
The coordinator invoked session `9b755390-8813-46c0-806f-130f997da955` with
only Read, Glob and Grep available, strict MCP configuration and no delegated
agents. The CLI completed successfully in 949257 ms over 215 turns.
This is source review, not an independent compiler run.

The prompt contained the 145-file primary packet plus instructions and guide
(648036 bytes). The immutable full packet held 564 selected files; another
560 compiler-import sources were available separately in its snapshot.
Availability is not a claim that Claude read all of those files. The local
transcript records 174 Read, 26 Grep and 14 Glob calls; exact file and line
coverage, including failed requests, is preserved in the adjacent coverage
record. Input hashes and the exact invocation are separately recorded.

The conditional verdict and identified gaps remain unchanged. Codex's
separate disposition records follow-up evidence and scope; evidence added
after this invocation is not represented as reviewed by Claude.

---

**Verdict for the narrow milestone: PASS as a conditional native rule.** The full supervisor `translateAddr` is proved from the source residue by `Xv6/Kernel/KptAddressProofs.lean:wp_translate`, with every component rule constructed natively in `KptAddressLink.lean:nativeSpec`. The seven hashed KptPublish files match the freeze receipt byte for byte and implement a genuine, but conditional, publication rule. I found no soundness blocker. The closure wording must stay conditional, and I list below what a translated `mycpu` or boot claim would still need.

## What I verified in the implementations

- **Nine-cell partition.** `KptAddressResources.lean:partition` is a bi-entailment between `cells (prepare rs data)` and the five auxiliary cells plus `dataCells`. The footprint expands to mstatus, cur_privilege, satp, pma_regions, pmpcfg_n, pmpaddr_n, htif_tohost_base, menvcfg, tlb, and `KptAddressGeometry.lean:unique` proves them distinct. `prepare` only overwrites the four residue keys; `prepare_status` and its siblings show each listed cell carries the owned value, and `RegisterPlan.fold` validates each read against machine authority via `RegisterWP.wp_read` and `power_read_register`. Nothing asserts equality of the whole file.
- **Residue open, close and preservation.** `open_residue` takes TOR from the owned PMP vectors only, through `tor_of_vectors`, which reads nothing but `entry0`/`upper0`. `preserved` fixes satp and both PMP vectors across every outcome; `close_residue` rebuilds `KptResidue.residue`, and `resources_close` returns the source existential residue. The updated TLB is re-snapshotted through `KptResidue.snapshot_intro` from the branch's coherence fact.
- **No hidden oracle.** `KptAddressSpec.lean:Spec.translate` takes only the certificate, five fractional cells, the residue, `mapAt`, the reservation fragment and the continuation. Maps, path geometry, PMP/PMA/HTIF configuration and the three walk configs are derived in `KptHardwareProofs.lean:mapped` by opening the invariant, checking `map_lookup` against the map authority and `KptGhost.agree` against the snapshot, and extracting RAM/alignment from the three owned slots.
- **Lookup and dispatch.** `KptTranslatePureProofs.lean:lookup_plan` is one TLB read; `lookup_mapped` derives residency and the cached A/D variant from `TlbCoherence.lookup_hit` plus `maps_det`; foreign tags fall to the miss via `match_TLB_Entry`, with no hash injectivity anywhere.
- **Hit.** `Sv39HitDefs.afterUpdate` returns PPN and PBMT from the original entry and refreshes only on `Ok (some word)`, matching generated `translate_TLB_hit`; `KptHitPure.lean:result_eq` and `coherent` close the loop.
- **Miss.** `KptTreeWalkNodeProofs.lean:wp_pointer` recovers the exact raw upper word from the nonleaf singleton family and continues with `global || globalBit raw`; `wp_leaf` picks the leaf A/D at the third read. `KptMissDefs.fillWord` fills cached, observed or written exactly as `update_and_write_pte` returns them, with `globalAfter` retained.
- **A/D.** `KptADProofs.lean:wp_update` keeps the real cached, gate, disabled, reread and written arms. Overlap retry and blocked writes come from `MemoryExclusiveWPProofs.lean:wp_exclusive_any` and `MemoryWriteWPProofs.lean:wp_checked` by Löb, matching `RiscvLang.v:799–910`. `KptWriteEventUpdate.lean:update` restores each byte's floor, allowed set and anchors through `slot_open`/`slot_close` and `slot_family`.
- **Masks.** Every invariant opening closes before the top-to-empty transition: `KptReadEventPower.lean:power_reads`, `KptExclusiveEventProofs.lean:current`, and the write update runs after `Hback` restores the full mask inside the later.
- **Guards, facts inside.**

| Path | Exposed memory guards |
| --- | --- |
| noncanonical | none |
| hit cached / disabled / reread / written | 0 / 0 / 1 / 2 |
| miss | 3 walk, then 0 / 0 / 1 / 2 |

`OutcomeFacts`, including `Selected` and `KptAD.BranchFacts`, sit under `KptAD.guarded` in `KptAddressDefs.finish`.
- **Exceptions.** `Sv39AddressPure.lean:exception` is kernel-checked against generated `translationException`; `noncanonical` executes the five-read prefix and returns the access-specific page fault; the suffix concatenates all 44 PPN bits with the 12-bit offset.
- **Capacities.** `KptOwnership.Capacity.ghost` derives views from `machine.era.views`; `KptPublish.contextCapacity` reduces to the same era heap/views/history, so no unmatched log or view authority exists.
- **ContextPinMint.** `ledger_mint` pays the None-to-pin move from the full timestamp authority with `pin_insert_ok`; `own_bound` needs only `Drained`; `boot_anchor` uses `Latest` plus `log_lookup` for the own-message arm rather than dirty membership alone, and pins each byte at its own timestamp with `floor ≤ g.log.length`.
- **Publication.** `KptPublishTreeProofs.lean:tree_boot` folds all 512 `KptOwnership.indices` per page and every present child by depth induction; the node claim and words are unchanged; `allocate_boot` then runs `KptShared.allocate`, which shoots both one-shot cameras and calls native `inv_alloc`. Anchors are derived, not assumed.
- **Round-eight base gap.** `State.lean`, `Node.lean`, `NodeProofs.lean`, `FetchRun.lean`, `Platform.lean`, `SupervisorPmpDefs.lean`, `Xv6/Machine/Boot.lean` and `compiler-imports/MachCSL/Machine/Image.lean` are present and consistent with the rule stack.

## Blockers, deviations, missing evidence

**Blockers:** none.

**Scope deviations to state in any closure wording**
- `KptAddressDefs.Ambient.pma` fixes `pmaBoot`; the source takes `pma_allows_all`.
- `Sv39Address.Effective` is fetch or MPRV zero, a subset of the source's effective-privilege premise.
- The access family is `KptLeaf.Supported` with `Allows`; the source quantifies `pte_check_ok`.
- ADUE, PBMTE and misa are arbitrary here, a generalization of `HartSKpt.v:swp_translate_kpt`.
- Both publication rules require `hartAgent cpu = 0`, as in the source; there is no log-top tree gate, matching the superseded source arm.
- The invariant namespace is a parameter; `kernelShared` fixes the source name.

**Publication is a conditional rule, not an inhabited allocation.** `allocate_boot` consumes `treeOwn (.user ξ) 2 (.own 1) tree`, `mapAuth era.kernelMap` with a pure `TreeSpec`, the two pending tokens at era names, the running context, and heap/TSO interpretations of a state `g`. `EraProofs.lean:allocate` only copies the three kernel names from a template. Nothing in the packet constructs the physical user tree, the concrete map authority, the tokens at era names, or an event site at which `heapAt g` is available.

**Missing evidence**
- Rocq files referenced by the pinned sources but absent from the packet: CtxValues.v, KptTree.v, KMap.v, PtAdBits.v, CommonWalk.v, PtreeType.v, HartBarrier.v, SRegime.v. Correspondence of `TsoPinnedRead.bootCredential`, `slotAnchor`, `TlbCoherence.entry` and `KptShared.TreeSpec` to their source definitions could not be checked against text.
- No KptPublish audit or build log is in `research-evidence/`; the receipt lists hashes and a count only. The three design documents named in the STATUS files are absent.
- No inhabitation witness for the composed rule or for publication; the "six kernel edge checks" are not supplied.

## Closure wording and remaining prerequisites

A concrete positive witness is not required to close the wording "native supervisor Sv39 translateAddr from the source per-hart residue, plus native private-tree publication as a conditional resource rule", provided the wording names the deviations above and says publication starts from an already-owned user-tier table. I recommend a small inhabitation check anyway: allocate the KPT ghosts first with `KptGhost.allocate`, feed those names as the era template, allocate a context with `TsoContext.allocate`, publish a one-page identity tree, and run one translation. Without it, joint satisfiability of `residue` and the publication premises rests on inspection.

A concrete witness is required, as in round eight, before any of these claims:
- **Translated `mycpu`.** A regime-parametric cycle layer, instruction fetch through this rule, and kernel text and stack resources.
- **Boot establishment.** Execution of `kvmmake`/`kvmmap` producing the user-tier tree and `TreeSpec` for the generated kernel map, tokens at era names, a publication event site replacing the source barrier leaf, `kvminithart` yielding `SatpRooted` and `EmptyTlb`, and the five ambient cells at their reset values, noting reset `menvcfg` is zero so kernel leaves must already carry A and D as in `HartSKpt.v:kpt_noupd`.
- **Cross-prover correspondence and the six roots.** Not addressed by this packet.

---

The review text above was written by Claude Fable 5.1. The framing, input records
and disposition were prepared by OpenAI Codex.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
