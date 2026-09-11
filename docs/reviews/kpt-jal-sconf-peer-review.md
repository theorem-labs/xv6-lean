# KPT JAL source-capability wrapper: independent review

**Final result: PASS for the closed native Link.** The earlier conditional
review is preserved below as historical evidence, with its original
reviewer attribution unchanged.

## Final native closure review

This additional review was performed by the separate Codex
`lean_logic_audit` agent. I read the new KptJalSconfLink and re-read all
four companion modules, the actual source WpSconfCtl237–281 boundary,
and the used source packet/cycle contracts. I authored some transitive
resource/function adapters; this review concerns the coordinator's five
wrapper modules and does not claim independent authorship of every
transitive dependency.

`nativeSpec` now supplies `KptJal.nativeSpec capacity` to the private
conditional composition. `nativePureSpec` supplies the three checked pure
laws, and `registrySpec` specializes the same actual capacity. No JAL
component WP remains in either public native theorem. The complete actual
fetch/decoder/body/retirement/clock implementation is therefore part of
the final theorem's dependency cone. Resource restoration and all guarded
continuations remain exactly those reviewed below.

The public source specialization remains disabled SIE, destination x1,
full tier and an explicit retained same-hart boot-PMA cell. The input
still requires actual JAL code and target-even; it does not require a
minimum stack depth, successful fetch/configuration premise or selected
successor. This closure does not establish source-entry resource
inhabitation, boot reachability or whole-kernel safety.

The owner reported the final target build GREEN1,221 jobs. My fresh
independent audit checked **all32 declarations across all five physical
modules**, including full types, opaque bodies (`allowOpaque := true`) and
constructors. Only propext/Classical.choice/Quot.sound occur; no
unsafe/partial dependency and zero exclusions. Reviewed source hashes
were unchanged across the audit. Evidence under
`/tmp/xv6-lean-research`: `KptJalSconfNativePeerAudit.lean`,
`kpt-jal-sconf-native-peer-audit.log`, `KptJalSconf-native-peer.sha256`.
No Lean changes requested or made. The coordinator confirmed updating
owner STATUS/design to the actual native closure scope.

## Earlier conditional review (preserved)

Result: **PASS for the explicit conditional wrapper**. The reviewed `wp_cycle` and `actual` require `KptJal.Spec capacity`. These four modules do not close that premise; no completed native JAL rule is claimed by this review.

The reviewing Codex subagent independently read all four coordinator-authored modules, the actual `KptJal` definitions/specification, the native `SieOffPacket` and `MycpuKptEntry` resource contracts and implementations used here, the completed-cycle register projections, and the fetch-guard introduction rules. The reviewer authored some earlier resource adapters; this is an independent review of the coordinator's new wrapper, not a claim that every transitive dependency was authored by a different agent or freshly source-reviewed here.

## Source comparison

Pinned source: `.upstream/xv6iris` at `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

- `iris/WpSconfCtl.v:237–282`, `wp_jal_s_sconf`: the source updates the selected nonzero, non-SP, non-TP destination to `pc + 4`, preserves the stack capability, and resumes at `pc + sign_extend imm` with the target-even premise. This wrapper specializes the destination to x1, SIE to false and tier to full. `stack` preserves x2 directly; `saved` proves the actual saved-register list is unchanged. It imposes no lower bound on the available stack words.
- `iris/IntrDefs.v:2937–2945`, `rd_ok`: the fixed x1 destination avoids both SP and TP. Source HartTp pinning is retained through the native packet/file predicates rather than replacing TP by an arbitrary physical-register value.
- `iris/WpNext.v:54–78`, `wp_next` / `wp_next_off`: the source disabled branch fixes the original hart. The wrapper retains that same hart and quantifies the actual next-cycle clock choice. It supplies an unguarded terminal continuation and introduces the execution's required laters internally.

The scope is deliberately narrower than the source's arbitrary allowed destination, arbitrary SIE bit and tier. General source PMA ownership remains inside the source capability. The additional same-hart discarded `pma_regions = pmaBoot` cell is explicit in both input and restored output; it is the current execution specialization, not a silent strengthening of `sconf`.

## Resource and execution checks

`open_packet` extracts the actual 50-cell packet and source remainder. Full-tier admissibility eliminates the Bare arm. Configuration and generation facts come from these owned resources; native register agreement with the retained boot-PMA cell supplies the required PMA equality. No independently assumed configuration, successful translation, receipt, memory value or instruction-result premise appears at this boundary.

The wrapper passes the actual KPT packet, code ownership, running context and an existential original reservation to the conditional JAL cycle contract. The entire original stack, timer capability, tier witness, whole persistent hardware bundle, translation shot and arbitrary caller frame are retained as its frame. It does not extract stack words or spend overlapping register ownership.

The continuation handles every trace introduced by `fetch_guards_intro`: the underlying guard fold retains one or two fetch chunks, hit/miss alternatives and each A/D guard case. The wrapper does not choose a successful lookup or receipt. `Completed` transports PC and nextPC to the target while preserving precisely the non-clock supervisor fields needed by `Boundary`. Reassembly uses the returned packet, the unchanged SP, the returned `none` reservation and all retained source components. The actual receipts returned by the callee may be discarded under Iris's affine logic; none are fabricated or required from the caller.

There is no new invariant opening in this wrapper. Masking and actual event execution remain obligations of the explicitly supplied `KptJal.Spec` implementation. The native entry/packet adapters used for resource restoration are already implemented; no caller restoration callback replaces their proofs.

## Independent validation

Commands run:

```sh
PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.KptJalSconfProofs
PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/KptJalSconfPeerAudit.lean
```

The build passed **1160 jobs**. The independent physical-origin audit passed **29 declarations in four modules**, with no exclusions. It checked every declaration's axiom cone against `propext`, `Classical.choice`, and `Quot.sound`, and traversed types, opaque bodies (`value? (allowOpaque := true)`) and inductive constructors, rejecting unsafe/partial dependencies. A component specification used as an explicit theorem parameter is not a new axiom; the successful audit does not discharge that parameter.

Local evidence: `/tmp/xv6-lean-research/kpt-jal-sconf-peer-build.log`, `/tmp/xv6-lean-research/kpt-jal-sconf-peer-audit.log`, and the audit driver above.

Reviewed source receipt:

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `Xv6/Kernel/KptJalSconfDefs.lean` | 1937 | `5437dd8f0512fd12b6f4f61193beb412e225b43a2cf436987500011f450f9e2f` |
| `Xv6/Kernel/KptJalSconfSpec.lean` | 1260 | `cf9e2f505ab533fff9fc1a68646d22d38ca4d94a33c394160cdd0e648efd24b0` |
| `Xv6/Kernel/KptJalSconfPure.lean` | 1365 | `53a292280867b2bc0aef9d94d512956ab7d20b107f5ce321cae987a11ac94b93` |
| `Xv6/Kernel/KptJalSconfProofs.lean` | 3650 | `ad5abb45ee6cc51efa438a92c11eece9d193151377414cebf6cac9ce37b24399` |

No correction requested. The next closure check must review the actual `KptJal` implementation and the link that discharges `KptJal.Spec`; this report alone proves neither boot/resource inhabitation nor whole-kernel safety.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
