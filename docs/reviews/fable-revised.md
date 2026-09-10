# Fable 5.1 max: revised design review

Reviewer: Anthropic Claude Code, model `claude-fable-5-1`, effort `max`.
This is the reviewer's returned assessment, preserved for inspection.
Claims and recommendations are subject to [the coordinator disposition](fable-disposition.md).

**Verdict: APPROVE WITH REQUIRED CHANGES.** The architecture is sound and the seven coordinator dispositions stand, with one sharpened. I found no mathematical blocker. I could not run builds, so build and axiom claims are taken from the audits plus the presence of `.olean` outputs for all 13 root modules.

## Dispositions

1. **Keep `arxiv-v1`.** Accepted. My first review conditioned the HEAD recommendation on the tag's kernel corollary being closed under only the three initial-state hypotheses. The artifact audit confirms it is. Withdraw the HEAD pin.
2. **Native iris-lean at 4.32.2.** Accepted. The `Language` class carries observations and strong adequacy takes an observation list, so the paper's observable-trace root is expressible.
3. **One-instruction gate first.** Accepted, with one addition. The paper's language hardwires the kernel image: `boot_facts` at `RiscvLang.v:1325` loads all of RAM from `boot_image` and runs the reset program per hart. The Lean language must therefore be parametric in the boot image, with the exported roots instantiating the paper ELF. Otherwise the `jal x0, 0` gate forks the semantics.
4. **Explicit correspondence.** Accepted, and now resolvable concretely. In coq-sail V1, `internal_pick` is `choose_range 0 (len-1)` followed by `nth_error`, failing on out-of-range indices; `choose_type` of `ChooseRange` and `ChooseNat` is `Z`; the paper's Choose arm at `RiscvLang.v:942` ignores `choose_prop`. In the paper model at the tag, every choice site but one is an enum `internal_pick`, and the single `undefined_range` sits in `undefined_Phys_Mem_Access_Info`, which nothing references. An out-of-range Rocq resumption lands on `fail`, which has no arm and is non-reducible. Since the exported theorem asserts reducibility everywhere reachable, the Rocq proof already entails that no reachable configuration sits at such a node. Required handling: give `.choose (.fin _)` and `.choose .nat` no arm in the Lean relation, keep arms for bool, bitvector, int and string where types coincide, and add a static scan of generated choice sites that fails on any new kind. This is explicit, matches the Rocq obligation exactly, and is cheaper than an Int-typed erased variant. Write payload: the Lean request has `Option` value, Rocq's is plain. Require `some` in the write arm and give `none` no arm.
5. **Measure image and decoder costs.** Accepted. Current import is hex chunks decoded through lists and checked by `#eval`, so it is evidence only.
6. **Toolchain setup.** No comment.
7. **Conditional boot links; drop the S/M-hart writer claim.** Accepted. The disk arm at `RiscvLang.v:1426` appends a DMA message and writes RAM, so my earlier statement was wrong.

## Required changes

- **Audit scope.** `Audit.lean` checks only axioms. Before the generated model lands, it must also reject `partial`, `unsafe`, `implemented_by`, `extern` and unreviewed `opaque` constants in the cone of exported roots, and audit by package rather than by the two name prefixes.
- **Pin the Sail compiler.** `upstream.lock.json` has no Sail compiler entry. Record the compiler commit, the backend specialization template revision, and the exact generation arguments.
- **Name the completion target.** State the four exported roots and their verbatim hypotheses in the plan, and add the boot-image parametricity rule from disposition 3.
- **Choose rule and scan** as in disposition 4, recorded in the semantics file's enumerated-rules list.
- **Platform hooks.** Unbound externs should become a dedicated stuck event with an `Empty` result rather than reusing the generic unreachable error, so audits can tell unbound hooks from model assertions.

## Code observations

The TSO slice in `MachCSL/Memory/Defs.lean` matches the checked `TsoMemPa.v` definitions. The extensional byte map is a legitimate representation, though the eventual state must still support the RAM totality clause of `boot_facts`. Litmus proofs by `decide` are meaningful only because the image is a constant function, which is fine for sanity checks. The free-V1 library preserves every V1 request field and has no partial or unsafe definitions. A stock model generation of 136 files existed during my review at toolchain 4.29.0 with an empty lakefile, never compiled, and was removed before I finished. It contained no `partial`, `sorry` or `unsafe` hits, which is encouraging for the audit gate.

The remaining critical-path risk is not a design flaw but the unbuilt generator integration: only a signature template exists. Its exit criterion should be a full paper-configuration model generated against the free-V1 library, compiled at 4.32.2, with the site scan clean, before any language code depends on generated types.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
