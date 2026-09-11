# Kernel datum interface review

APPROVE for the bounded statements in the coordinator-authored `KernelDatumDefs.lean` and `KernelDatumSpec.lean`. This is an independent source/interface review, not a review of their future native implementation.

Read the complete pinned `Ktier.v`, `RiscvPtsto.v:1147–1262`, `TsoCtx.v:608–640` and the word definition at `TsoCtx.v:845–858`, together with the native `TsoContext.physPointsto` definition. The artifact pin is `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.

The order allows identity-to-full weakening and forbids the reverse. The identity pin is an equality between the claimed physical address and the virtual address; the full tier carries no such pin. The unsigned address bound is the source positive Sv39 half (`< 2^38`, including zero), not a strict positivity condition. The RW mapping claim and actual physical RAM requirement are retained.

The virtual byte wraps the existing native physical context byte, which retains the same-dfrac flat value and timestamp/pay-none fragment plus the exact lower-bound-or-dirty disjunction. No timestamp fraction is upgraded. The word keeps virtual eight-byte alignment and eight modular per-byte virtual addresses, each with its own mapping claim and physical context resource. It does not assume a single-page translation before proving the relevant geometry.

The seven resource fields are agreement, access with conditional reassembly, and tier weakening laws. The accessor's replacement byte must be supplied as an actual physical resource; it does not assert an update or translation can occur. Agreement across contexts first identifies the mapped PPN and then uses physical value ownership. No translation oracle, whole-state authority premise or physical mapping truth is hidden in these statements. No correction was requested.

The coordinator's signature build log reports 409 successful jobs. This brief review did not rerun that build or perform an implementation-cone audit; those remain distinct from this source check.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
