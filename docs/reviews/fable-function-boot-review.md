# Fable eleventh review: native function and boot text

The unchanged result below was returned by Claude Fable 5.1 through Claude
Code at max effort, session `54579143-869e-4699-954f-99c91876f104`. It completed successfully
in 826209 ms over 121 turns. Only Read, Glob and Grep
were available; no subagent or compiler invocation ran in this session.
The prompt supplied 101 primary files inline (651469 bytes
including instructions), with the complete staged project and pinned Iris
source tree available in the immutable snapshot for counterpart inspection. Supplied evidence is distinct
from independently executed validation.

The transcript records 120 tool calls: 71 Read,
39 Grep and 10 Glob. Exact returned ranges and file
hashes are recorded separately; availability does not imply complete reading
or declaration-cone inspection. Snapshot availability is distinct from observed file reading.

---

Review complete. Everything below comes from my own reading of the snapshot files, except where I say a log was supplied.

**Verdict: PASS for the stated conditional scope, no soundness blocker.** The four Link theorems are unconditional native constructors of their Spec structures, and each Spec matches the approved contract text I compared it against. The audit and build logs under `evidence/` are one-line supplied summaries that I could not reproduce; the build log is at least consistent with the module counts in the STATUS files.

## Function and wrapper

- **All fourteen phases are real.** The phase relation is built inside `chain` after each returned cycle rule and never appears as an input. Its successor uses the same body control, value map and word schedule that the cycle rule returns, so the two cannot drift.
- **Bare arithmetic is reused only through whole typed-file equality.** The theorem `body_entry` proves that the KPT body update, viewed through the pinned software map, is definitionally the Bare body file, and the Bare reference facts used afterwards are pure statements about symbolic files. No Bare WP, Bare configuration or physical-stack predicate enters the cone.
- **Anchor, saved words and loads.** Both virtual words sit at the fixed anchor, and the memory rule loads whatever the owned word holds. The saved RA becomes known after index one and S0 after index two, and the final schedule equals the original RA and S0, which is exactly the source's rewritten frame at the epilogue.
- **Thirteen callee-saved keys, TP result.** The exported result restores keys two and eight through the reference and proves all other keys except a0 and a5 untouched by a direct induction, which matches `CalleeSaved.v`. The a0 value is the source modular return expression at the pinned TP, and the numeric address agrees with the immediates in the pinned `KernelConsts.v`.
- **Clocks, guards, receipts.** Every cycle ends with a universally quantified next tick and an off-clock completion, all fetch and body guards are introduced without selecting a view or branch, and the receipts list is returned in index order.
- **Wrapper versus `SpecMycpu.v`.** The premise shapes match the source bundle: the interrupts-off arm is only the eighth-bit token, so the omitted process pointer is genuinely unused, and the source's hart-pinned continuation collapses to the unbound Lean form. The returned stack count, restored capability, low-bit-cleared return target, kernel text and frame are all handed back.

Deviations to state plainly:

- **Tier.** Only the KT1 instance is proved. The source contract is tier-generic, and the source tree's default callers resolve at KT0, so identity-tier callers in the KPT arm and all Bare-arm callers are outside this wrapper.
- **PMA.** The boot-table equality is a strictly narrower premise than the source's `pma_allows_all`. It is sound and inhabitable at the concrete cold boot, but no holder of the source capability alone can discharge it, so the boot chain must export that discarded per-hart cell.
- **Receipts and code windows** are dropped at the wrapper boundary. That is legitimate in the affine logic and costs nothing, but the wrapper contract is weaker than the function contract.
- The JAL-callable form is not ported, as the packet says.

## Boot text and map installation

- **Extraction accounts for every client.** I checked the era client columns against the retained bundle: both deleted maps, the log receipt, register cells, metadata tokens, device fragments, disk bytes and reservation fragments all survive, so the affine proof mode did not silently drop anything.
- **No byte or timestamp oracle.** Each lookup is derived from the actual boot state through the ELF correspondence and the decoder equation, and timestamp zero comes from the real boot timestamp map.
- **Sparse carve versus source.** This produces the named text map only, not the source's whole sub-etext split. That is disclosed, and the holes stay owned in the remainder.
- **Map installation order is correct.** The static map is allocated first, its name is written into the template, the era allocator returns auxiliary-name agreement, and identity text is attached without any name equality assumed as input. No page table, one-shot or translation receipt is manufactured.
- The `produce` field parses as a pending update beside the retained bundle, which is the stronger reading, and the combined-update corollary is proved by framing. Fine.

## Gaps and next steps

- **Missing source evidence.** The pinned `KernelInstrs.v` and `KernelSyms.v` are not in the snapshot. The code-map domain therefore rests on the generator's host-side count check plus the kernel-checked ELF certificates, not on my inspection of the Rocq map. The BootCarve comments giving an older byte count and end address are stale relative to the pin, so they should not be cited.
- **Inhabitation is open.** The configured witness uses a two-leaf table that does not inhabit the shared invariant or static map, so it is not evidence that the wrapper's input can be allocated. This is correctly stated in the packet.
- **Documentation.** The project status page has no validation paragraph for this batch, unlike the previous three; the supplied audit totals should be recorded there. The ProcGeom comment giving a different `cpus` address is also stale and cannot be cross-checked without `KernelSyms.v`.

Closure wording I would accept: "conditional native full-tier source mycpu wrapper with an explicit same-hart boot-PMA fragment, and native sparse boot-text plus static-map-name allocation in the actual era; no inhabited entry state, physical page table, JAL caller, identity-tier or Bare-arm coverage, and all six whole-system roots remain open."

Priorities: export the discarded boot-PMA cell from the boot chain, add the identity-tier KPT-arm and Bare-arm wrappers or a tier-generic dispatch, port the JAL-callable form, and add `KernelInstrs.v` and `KernelSyms.v` to future review snapshots.

---

The review text above was written by Claude Fable 5.1. Framing and evidence
records were prepared by OpenAI Codex.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
