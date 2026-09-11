# Independent review of push_off scalar bodies

PASS for the declared normalized-body milestone; no implementation correction requested. This review was performed by the Codex `artifact_audit` agent independently of the `lean_logic_audit` agent who implemented the family. All six frozen modules (`PushOffScalarDefs`, `Spec`, `Pure`, `Plan`, `Proofs`, `Link`), their design and STATUS were read in full. The implementation and relevant source files match the author's freeze hashes and the implementation hashes captured before this review.

The source comparison used pinned `CodePushOff.v` and the surrounding `ProofPushOff.v` instruction context, together with actual generated `InstsEnd.lean`, `BaseInsts.lean` and `ZicfilpRegs.lean`. The reviewed body plans cover precisely indices 0, 4, 6, 9, 12, 17, 18, 20, 21 and 23. They implement modular stack subtraction/addition, frame-pointer calculation, status copying, full-width zero comparison, ADDIW low-word truncation and sign extension, JR, logical right shift, bit masking and the backward jump. They reuse the frozen source AST inventory; this family itself proves the actual normalized `execute` expansion. Fetch and compressed decoding are separate previously reviewed families.

The branch uses the actual register value: an untaken BEQ preserves the prepared nextPC and performs no spurious PC/MISA reads. A taken BEQ and the backward jump retain generated alignment checks and eager reads. JR reads the real RA, clears its low bit, and preserves RA because its link destination is x0; both JR and the backward jump retain the actual eager nextPC read. JR's supervisor/LPE-disabled/MISA.C premises match the reused actual return plan. Arithmetic bodies require no hardware-value premise. The source-config projection discharges the stated control premises from source MISA, MENVCFG and instruction-address facts; it does not assert a broader source capability.

`body_eq` supplies ten kernel-checked conversions to actual generated execution. The finite plans then use real register-read/write constructors, rather than a supplied evaluator-success assumption. Full register-file equality connects the physical successor to the logical GPR/control updates, including every unmodified register. The native body rule partitions and restores the same fifty-cell packet, retains its exact Bare/KPT regime and translation resources, and frames the literal caller resource unchanged. Native mstatus ties and pinned TP survive through the existing packet laws. The final Link discharges all implementation contracts; its remaining WP premise is the genuine continuation after the actual body.

Independent validation:

- Fresh native build: 931 jobs, PASS.
- Strict audit: all 201 physical-origin declarations across the six modules, including private declarations with `setExporting false`; recursive type, opaque-body and constructor traversal. Only `propext`, `Classical.choice` and `Quot.sound`; no unsafe/partial dependency and zero exclusions.
- Replayed all sixteen owner edge checks: modular SP wrap, ADDIW overflow/truncation, logical shift, mask, taken/untaken BEQ including a nonzero high word, odd/maximal RA, backward wrap and symbolic RA preservation.
- Five additional actual-plan specializations check high-word ADDIW truncation, logical high-bit shift, both BEQ outcomes and odd RA. These instantiate the proved actual program plan and verify its observable endpoint; they are not separate evaluator certificates.
- All six implementation hashes and the five recorded source hashes match their frozen receipts.

Evidence remains under `/tmp/xv6-lean-research`: `PushOffScalarPeerAudit.lean`, `PushOffScalarActualChecks.lean`, `push-off-scalar-peer-{build,audit,checks,actual-checks}.log`, `push-off-scalar-peer-results.json`, and the author's `push-off-scalar-{freeze,source}.sha256`. Raw whole-body evaluator probes were stopped because repeated dependent-register normalization was expensive; they provide no claimed validation result. The successful final checks above use ordinary kernel proofs.

This establishes actual normalized register-only body WPs. It does not establish fetch, retirement, clocks, a complete push_off cycle/function, enabled-SIE behavior, migration, or inhabitation of source entry resources. Literal frames remain anchored exactly as supplied; the rule does not silently reinterpret stack resources after an SP update.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
