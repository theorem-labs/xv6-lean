# Mycpu JAL-call native composition: independent review

**Final result: PASS for the closed native call Link.** The earlier
conditional review and its accurate reviewer authorship statements are
preserved below as historical evidence.

## Final native closure review

This additional review was performed by the separate Codex
`lean_logic_audit` agent. I read the new MycpuCallSconfKptLink and all four
complete companion modules, and rechecked SpecMycpu58–78,
ProofMycpu320–353 and WpSconfCtl237–281. I authored some earlier transitive
function/resource adapters; the review is of the coordinator's final call
composition, not a claim that every dependency has different authorship.

`nativeSpec` supplies the actual KptJalSconf.nativeSpec,
KptJal.nativeResourceSpec and the proved local pureSpec. The function
callee in wp_call is already the actual MycpuSconfKpt.nativeSpec.
Consequently no JAL, code-producer, pure-specification or body-execution
interface parameter survives the public nativeSpec/registrySpec.

The actual input code supplies PC alignment. Target equality derives the
JAL target-even condition and transports the returned source capability
to the actual mycpu entry. The genuine JAL continuation universally
introduces the body clock choice; the genuine function continuation
universally introduces the next clock choice. The modular link-alignment
proof makes low-bit-clearing leave PC+4 unchanged. Saved13 transitivity
and unchanged pinned TP produce the final result. Original source stack
count, function text, JAL code, same-hart boot-PMA and caller frame are
all restored exactly. No intermediate successful execution or physical
stack assumption is introduced.

This is the full-tier, disabled-SIE, destination-x1 source call with n≥2
and exact target equality. It remains explicitly specialized to boot-PMA;
entry resource inhabitation, boot reachability and whole-kernel safety do
not follow from native closure alone.

The owner reported the final target build GREEN1,221 jobs. My fresh
independent audit checked **all33 declarations in all five physical
modules**, full type/opaque-body (`allowOpaque := true`)/constructor cones,
standard propext/Classical.choice/Quot.sound only, no unsafe/partial
and zero exclusions. All reviewed source hashes remained unchanged.
Evidence under `/tmp/xv6-lean-research`:
`MycpuCallSconfKptNativePeerAudit.lean`,
`mycpu-call-sconf-kpt-native-peer-audit.log`,
`MycpuCallSconfKpt-native-peer.sha256`. No Lean changes requested or made.
The coordinator confirmed updating owner STATUS/design to actual native
closure; the final peer-review status can now be marked PASS.

## Earlier conditional review (preserved)

**PASS for the explicit conditional composition.** The reviewing Codex subagent independently read the coordinator-authored `MycpuCallSconfKptProofs.lean` against all three companion modules and the actual callee contracts. The reviewer authored the companion pure proofs, already reviewed separately by the coordinator; this report does not label those proofs independently authored.

Source: `.upstream/xv6iris` pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, complete `SpecMycpu.v`, `ProofMycpu.v:320–353`, and `WpSconfCtl.v:237–282`. The source call writes x1 to PC+4, calls mycpu with unchanged stack availability and disabled SIE, and composes the thirteen callee-saved equalities and pinned-TP return formula.

`wp_call` obtains alignment from the actual input JAL code. It passes kernel text plus the arbitrary caller frame through JAL, then passes the original JAL code plus the same caller frame through the already closed `MycpuSconfKpt.nativeSpec` function. Both calls retain the actual same-hart boot-PMA resource. The target equality transports the returned source capability to the real mycpu entry; the proved modular return-PC equality transports the final capability to PC+4. The final result is obtained by saved-register transitivity and TP pinning, not by assuming the function's output.

Both clock choices remain universally quantified in the genuine continuations. No intermediate configuration, success, receipt, stack contents or restoration oracle is introduced. The full source capability and all input text/code/PMA/frame resources are reassembled exactly, and the stack requirement is precisely the function's n≥2 requirement.

The theorem is **conditional on `KptJalSconf.Spec`, `KptJal.ResourceSpec` and `PureSpec`**. The pure implementation exists; the function callee is linked to its actual native implementation. This four-module review does not discharge the remaining JAL component parameters or claim a completed native call Link, operational/resource inhabitation from boot, or whole-kernel safety.

Independent validation:

```sh
PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.MycpuCallSconfKptProofs
PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/MycpuCallSconfKptPeerAudit.lean
```

Build: **1208 jobs passed**. Audit: **30 physical declarations across Defs/Spec/Pure/Proofs**, including private/generated declarations. All axiom cones use only `propext`, `Classical.choice` and `Quot.sound`; full types, opaque bodies (`allowOpaque := true`) and constructor traversal found no unsafe/partial dependency, with zero exclusions. Successful axiom auditing does not discharge explicitly quantified component specifications.

Local logs: `/tmp/xv6-lean-research/mycpu-call-sconf-kpt-peer-build.log` and `/tmp/xv6-lean-research/mycpu-call-sconf-kpt-peer-audit.log`. Companion source hashes are in the earlier interface report. Reviewed native proof SHA-256: `bef4e1e37e0c710fb37e225f62a535b2d747853fad85ff6d40ac5cb12f37126e` (2803 bytes).

No correction requested. No production source or umbrella edits made for this review.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
