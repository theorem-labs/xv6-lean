# Virtual datum word: independent review

PASS for the complete coordinator-authored `KernelDatumWord{Defs,Spec,Pure,Proofs,Link}.lean`, its STATUS and `kernel-datum-word-boundary.md`. No correction was requested. The reviewing Codex agent implemented earlier context/memory and KPT dependencies, which were reviewed separately; it did not author this five-module bridge.

Read the full five modules, the underlying `KernelDatum` definitions/proofs, native `TsoContext.physPointsto` and `TsoContextWord.pointsto`, and pinned `TsoCtx.v:845–940`, together with the byte definition at 608–640 and `RiscvPtsto.v:1147–1262`/`Ktier.v` reviewed for the datum interface. The source pin is `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The four pure laws retain all 64-bit virtual addresses and all 44-bit PPNs. Eight-byte alignment ensures the page offset is at most 4088 and prevents the eight-byte window from wrapping even at the top of the 64-bit range. `vpn_offset` therefore identifies the eight actual virtual VPNs. `physical_nat` proves the full PPN-plus-offset value, and `physical_offset` and `physical_aligned` derive the physical word geometry without an identity pin or assumed translation result.

The native proof first borrows the zero-index byte, extracts its persistent mapping claim, and restores the original word. For every byte, `normalize_byte` uses the actual ghost-map agreement at the proved equal VPN to identify its PPN with the first one. It retains that byte's original positivity, RAM and tier-pin facts and its unchanged physical context resource. It does not replace the eight claims with a weaker head-only claim.

The separating conjunction is then rearranged into all eight persistent claims and exactly the existing physical context word at the same era, context, fraction and value. The closing wand retains only persistent claims; it requires a replacement physical word with the same context and fraction. No physical byte or mirrored timestamp ownership is duplicated, allocated, upgraded or moved between contexts. The separate `close` and `head` contracts are implemented directly, and `nativeSpec`/`registrySpec` supply all resource fields.

This is a resource bridge. It does not prove that an instruction translates or reads memory, omit the A/D events those operations may need, or establish a virtual stack allocation. The STATUS correctly keeps those obligations separate.

Independent validation: `python3 tools/lake.py build Xv6.Kernel.KernelDatumWordLink` passed (658 jobs). `/tmp/xv6-lean-research/KernelDatumWordPeerAudit.lean` independently checked all 45 physical declarations across the five modules and their full type, opaque-body (`allowOpaque := true`) and constructor cones. Only `propext`, `Classical.choice` and `Quot.sound` occur; there are no unsafe/partial dependencies or exclusions. Logs: `kernel-datum-word-peer-build.log` and `kernel-datum-word-peer-audit.log` in the same research directory.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
