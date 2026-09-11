# Fable tenth review: missing-source supplement

The unchanged result below was returned by Claude Fable 5.1 through Claude
Code at max effort, session `fb1e3441-498b-4dce-9a1f-f995702ec55a`. It completed successfully
in 634513 ms over 73 turns. Only Read, Glob and Grep
were available; no subagent or compiler invocation ran in this session.
The prompt supplied the previous verdict and full 35-file supplement
(528865 bytes including instructions), with the original immutable
snapshot available for counterpart inspection. Supplied evidence is distinct
from independently executed validation.

The transcript records 72 tool calls: 34 Read,
31 Grep and 7 Glob. Exact returned ranges and file
hashes are recorded separately; availability does not imply complete reading
or declaration-cone inspection. Original round-nine inputs remain unchanged.

---

**Verdict: unchanged. PASS as a conditional native rule, no soundness blocker.** The eight Rocq files close every "could not be checked against text" item from the prior review, and the four named definitions correspond exactly. The publication validation evidence is now supplied and internally consistent. Nothing in the supplement inhabits the composed rule or the publication premises, so the conditional wording and the boot, translated `mycpu`, and cross-prover limits stand as written.

## Source correspondence, now checked against text

| Source definition | Lean counterpart in the snapshot | Result |
| --- | --- | --- |
| `CtxValues.cv_boot_cred` | `MachCSL/Logic/TsoPinnedReadDefs.lean:25` `bootCredential` | Exact: view receipt at the hart's agent, or agent-zero plus a log-length lower bound. |
| `CtxValues.cv_own` | `TsoPinnedReadDefs.lean:17` `ownAnchor` | Exact: one-based position, log fragment, byte written at the address, author equals the agent. |
| Anchor disjunct of `PtTree.kpt_slot_pin` | `TsoPinnedReadDefs.lean:30` `slotAnchor`, folded by `slotBytes` at line 36 | Exact three arms: floor zero, agent-zero own message, agent-zero view receipt. `KptOwnershipDefs.lean:56` `kernelSlot` reproduces `kpt_slot_pin` including the alignment conjunct. |
| `CtxValues.cv_slot_read_ok` | `TsoPinnedReadProofs.lean:127` `slot_read` | Same four-way case split; the own-message arm rewrites the hart agent to zero before `author_read`, as the source does with `H0`. |
| `CommonWalk.u_walk_entry` | `TlbCoherenceDefs.lean:21` `entry` over `Sv39TlbDefs.lean:9` | Exact after the source's masks reduce: sign-extended tag, zero level mask, PPN of the leaf, raw leaf word, level-zero slot address, global bit accumulated from `false`. Field order matches the generated `TLB_Entry`. |
| `PtTree.tlb_cache_of`, `tlb_ok_pt` | `TlbCoherenceDefs.lean:26` `CacheOf`, `Coherent` | Exact, quantified through the hash with no injectivity. |
| `KptTree.kpt_tree_spec_gen` | `KptSharedPureDefs.lean:8` `TreeSpec` | Exact. `KptLeaf.word ppn pc a d` equals `pte_set_ad (mk_pte ppn (kperm_flags pc)) a d` by `KptTree.v` `kperm_set_ad_leaf` with the bases 0x0B and 0x07 from `KptPt.v:437`. |
| `PtAdBits` laws | `MachCSL/Machine/PteCanonicalBits.lean`, `PteCanonicalProofs.lean` | `setAD`, `canon`, the bit reading, absorption, canon inversion, high-byte stability and the four-element byte-zero class all match. |
| `PtreeType.ptree` | `Xv6/Kernel/PtTreeDefs.lean:21` | Exact. |
| `KMap.kmap_auth`, `kmap_at`, lookup, insert | `MachCSL/Logic/KptGhostDefs.lean:70` onward | Exact, name-parametric. |
| `KptShare.tlb_res_pt`, `kpt_creds`, `kpt_body` | `KptResidueDefs.lean:43`, `KptSharedDefs.lean:25` | Exact conjunct for conjunct. |
| `SRegime.s_acc_ok`, `kpt_satp_ok`, `pmp_ent0_ok` | `SupervisorBare.Supported`, `KptResidue.SatpRooted`, `SupervisorPmp.TorRam` | Exact, including the strict-positive lower bound and the RAM-coverage bound. |
| `HartBarrier.pub_step`, `ghost_step` | `compiler-imports/MachCSL/Logic/BarrierWPDefs.lean` | Definitions exact; no barrier leaf theorem exists in the snapshot, see below. |

## Deviations, refined by the new text

- **Access family is a match at the regime tier.** `SRegime.v` `res_absorb` and `kpt_swp_translate` take `s_acc_ok` plus `kperm_allows` and discharge the A/D-quantified check with `kperm_variant_check`. The Lean `Supported` plus `Allows` premise is that interface. Only the lower `KptTree`/`HartSKpt` lemmas quantify `pte_check_ok`.
- **PBMTE, ADUE and misa.** `HartSKpt.v:961–962` fix PBMTE zero and ADUE one, and `SRegime` fixes `menvcfg = MENVCFG_S` and `misa = MISA_C`. The Lean rule leaves all three arbitrary: `KptLeafPlan.lean:31` reads them through `readAny`, `check_plan` splits the PBMTE branch, and `KptADDefs.lean:41` carries an explicit disabled arm returning the real `PTW_PTE_Needs_Update` error. This is a sound generalization. At reset `menvcfg = 0` the source theorem does not apply at all, while the Lean rule applies and gives the cached translation for A/D-preset kernel leaves and the exact fault otherwise. Establishing the actual ambient value remains a boot-stage obligation, as the supplement says.
- **PMA** stays a specialization: `pma_allows_all` on the exec lane and `pma_allows_ram` on the swp lane versus the fixed `pmaBoot`.
- **Effective privilege**: the source discharges it with MPRV zero for every access; Lean's fetch-or-MPRV-zero is slightly more general there and slightly narrower than the raw `sr_absorb` premise.
- **Not ported, unchanged scope**: the `s_regime` record and regime-parametric layer, the static map `kmap_M0` with its claim bundle and tier bridge, `ctx_values` and `cv_cred`, and the barrier leaf rules. The snapshot has the barrier node step at `MachCSL/Machine/Node.lean:97` and the client obligations, but no counterpart of `wp_hart_barrier_gs` and no call site running publication inside a `ghostStep`. `Pt4kWalk.v` is still absent; `mk_pte` is pinned only indirectly through the rewrite chain in `KptTree.v`.

## Evidence and gap status

- The seven publication files match the round-nine manifest hashes and the receipt. Build log ends at job 721 of 721. Owner and root audits agree on 76 declarations with zero exclusions; the root audit disables exporting and traverses opaque bodies.
- The six checks replay with exit code 0 and the recorded source hash. They are local lemmas only: the word-zero case is in fact a nonleaf singleton, and the out-of-width byte is the zero extension. The replay ran in the mutable working tree and does not hash the built modules, a minor caveat since the definitions involved are unchanged in the snapshot.
- The three designs named by the snapshot's ContextPinMint, Sv39Address and KptPublish STATUS files are supplied. KernelDatum, KernelDatumWord and KernelStack describe modules absent from the snapshot and were read as context only. ContextPinMint's own build and audit logs are still only named, not supplied.

Closed: all eight missing sources and the four correspondence checks; publication build and audit logs; the six checks; the design documents. Remaining, unchanged from the prior review: an inhabitation witness, a publication event site with a barrier leaf, boot establishment of the tree, `TreeSpec`, era-name tokens, `SatpRooted`, `EmptyTlb` and the ambient cells, translated `mycpu`, and cross-prover closure.

---

The review text above was written by Claude Fable 5.1. Framing and evidence
records were prepared by OpenAI Codex.

*Authorship note: this was researched and written by an AI coding agent (OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is posted from this account.*
