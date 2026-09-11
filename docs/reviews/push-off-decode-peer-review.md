# PushOffDecode independent peer review

PASS for the declared finite decoder and compressed-expansion boundary. No implementation correction is required. This review was performed by the independent Codex sail-audit agent; the six implementation modules were authored by the artifact-audit agent. Fable round 12 did not cover this scope.

## Material reviewed

Read all six `Xv6/Kernel/PushOffDecode{Defs,Spec,Certificates,Plan,Proofs,Link}.lean` modules, their STATUS and design, the entire `PushOffCodeDefs.lean` source table, and pinned `iris/CodePushOff.v`. Compared the source decoder contracts in `KernelDecode04.v` (`kd_1101`), `KernelDecode17.v` (`kd_100177f3`), and `KernelDecode22.v` (`kd_0014d793`). The source revision is `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476` (`arxiv-v1`). Also inspected the actual `snapshotPlanRun`, snapshot coverage, and their soundness definitions.

## Contract and proof findings

All 24 indexed instructions match the source decoded and normalized constructors: 19 compressed instructions and five base instructions. This includes the three distinct positive JAL offsets, signed four-byte loads, four-byte stores, the CSRRC immediate instruction, and the final negative compressed jump. Compressed expansion proves the actual generated `ExecuteAs` result; executing the normalized instruction remains a separate obligation.

The public `decode` law supplies a finite plan for the actual generated decoder and preserves the complete register file. Its footprint records owned keys rather than event occurrence counts. Repeated eager register reads remain in the generated program. Compressed rows use the MISA cell; base rows use the actual supervisor privilege and MENVCFG cells. All unrelated register values remain arbitrary. Fractional shares are carried by the footprint without claiming an allocation or resource validity theorem.

The compressed configuration fixes the full source hardware MISA value. Some Rocq compressed decoder lemmas need only the C bit. This is a documented specialization, not a proof of those weaker general contracts. Base rows do not require MISA because the checked actual Lean decoder does not read it on these paths. Their supervisor/MENVCFG specialization is explicit.

The non-JAL certificates construct ordinary reflexivity proof terms checked by Lean's kernel. There are 19 fresh certificates and two reused equal cases: the repeated C.LW and existing identical C.JR. The three JAL rows instead reuse the general checked JAL decoder factor and derive the exact small register plan, avoiding a replacement decoder or supplied success fact.

The private snapshot-to-plan proof inducts over fuel and all event constructors. With the supplied constantly absent memory oracle, success admits only covered, owned register reads. It rejects missing register values, memory events, writes, and every other unsupported event. Coverage and footprint membership are proved from the row configuration internally. The finite 24-case dispatch uses this soundness theorem or the checked JAL factor for every row. `nativeSpec` supplies all six public contracts with these implementations; it does not assume a decoder WP or success oracle.

## Independent validation

Rebuilt the final Link successfully: **1,128 jobs**. A fresh strict audit covered **83 physical declarations in all six modules**, including private and generated declarations. It traversed declaration types, values with `allowOpaque := true`, and datatype constructors, with exporting disabled. All transitive axioms are among `propext`, `Classical.choice`, and `Quot.sound`; no unsafe or partial dependency, initial allocator dependency, or exclusion was accepted.

Eleven additional kernel-checked fixtures passed, with an enforced foundational-axiom allowlist:

- Missing MISA rejects the actual compressed decoder.
- Missing MENVCFG or privilege independently rejects the actual CSR decoder, confirming eager reads are not erased.
- Zero fuel rejects evaluation, and a register write is rejected by the certificate evaluator.
- Changing `0x1101` to `0x1141` changes the actual decoded stack immediate from −32 to −16; the altered AST differs from the source row.
- Counts are exactly 19 compressed and five base rows.
- The final normalized jump has immediate `0x1fffe0` and destination x0, and the normalized load at offset `0x14` is signed and four bytes wide.

The fixture file initially had two local elaboration mistakes (an unavailable instruction decidability instance and an incorrect scratch LOAD constructor shape). Both were corrected before the successful check. No production file changed.

Evidence retained under `/tmp/xv6-lean-research/`:

- `push-off-decode-peer-build.log`
- `PushOffDecodePeerAudit.lean` and `push-off-decode-peer-audit.log`
- `PushOffDecodePeerChecks.lean` and `push-off-decode-peer-checks.log`
- Owner freeze manifest `push-off-decode-frozen.json`; all six hashes independently rechecked unchanged.

## Scope

This establishes the finite actual decoder plans and compressed expansion for the explicit source configuration. It adds no fetch, memory-access, normalized-body execution, CSR-effect, cycle, function-WP, source boot allocation, or full `push_off` theorem. Those remain separate consumers. The existing code-byte resource layer is referenced, not re-proved by these decoder certificates.

## Reviewed implementation hashes

| File suffix | SHA-256 |
| --- | --- |
| `PushOffDecodeDefs.lean` | `de7210daa7dc05b9f9a1661c1edaea51aac49da3919ad8af2829bdea0803d6f8` |
| `PushOffDecodeSpec.lean` | `5d0ed1550a6402efbcdaec79ffc5cae9f0879a078a82d9023b0ce1d32c72b6ad` |
| `PushOffDecodeCertificates.lean` | `5e54c4d3ebaf3c5c1264abe141ff2bbd2daa6b748665ff7b6d5ce657bbf58450` |
| `PushOffDecodePlan.lean` | `ca0a7bfa13865b85bb2836b9774af24b00db49791f6859fedfc9f0464dd3f6eb` |
| `PushOffDecodeProofs.lean` | `3f9e1d7917fa2421ff3b61d8b5fed3ef310efdf45d3f275c22f9fb70d5adf202` |
| `PushOffDecodeLink.lean` | `5da1785937e45b9f18b82b069ffd9c71bdeaa46c56a6dab2eff10394e159a47a` |

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
