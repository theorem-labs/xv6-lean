# Independent review of push_off's disabled sstatus CSR body

PASS for the declared actual-body scope; no implementation correction requested. The Codex `artifact_audit` agent independently read all six root-authored PushOffCsr modules: Defs, Spec, Pure, Plan, Proofs and Link. This extends the earlier signature-only review to the complete native implementation.

The concrete source instruction is push_off+0x0a, index 5: CSRRCI sstatus, immediate 2, destination x15. Comparison covered CodePushOff.v, ProofPushOff.v's corresponding step, WpSconfCsr.v's generic execution lemma (1633 onward) and disabled branch of wp_csrci_sstatus_s_sconf (4420 onward). The latter also handles source interrupt-count/resource transitions; this family deliberately proves only the actual disabled register body. Generated execute_CSRImm/doCSR, read_CSR/write_CSR, check_CSR_result and its CSR privilege/access/stateen helpers were inspected directly, along with the existing legalizer and native packet/register dependencies.

The full plan follows the real generated sequence: privilege read, actual CSR access check with its MISA reads, second privilege read, original mstatus read, pre-write mstatus read and actual legalizer, physical mstatus write, post-write mstatus read, and x15 write. The old sstatus view supplies x15, while the post-write view supplies the write callback. Neither read is replaced by the other. Source-supported landing-pad handling preserves arbitrary saved SPELP/MPELP bits. MsFacts excludes invalid MPP=2 from the identity claim; nominal 0/1/3 remain covered. No MENVCFG-zero, reserved-bit-zero or unrelated-file premise is added.

The private access-check certificate is ordinary kernel-checked definitional equality. Its soundness lemma permits only actual owned register reads: its memory oracle is identically none, and every unsupported event is rejected. The public plan has no evaluator-success, snapshot-coverage or component-WP premise. Fractional privilege/MISA cells can be read repeatedly; mstatus and x15 require full cells for the actual writes. Although mstatus returns unchanged, the write constructor remains present before the full-file write-self equality is used.

The native proof derives MsFacts and SIE=0 internally from the actual packet. The half SIE tie and disabled eighth use the exact same era/hart ghost name. Pure agreement extracts a fact while the original bit resources remain available for reassembly; it does not mint or duplicate linear ownership. The fifty distinct physical cells are partitioned once, folded through the actual register plan, and restored with the original mstatus ties, translation regime, x0 fact and literal caller frame. The complete entry-file equality ensures that x15 is the only final physical change. TP and every other GPR are preserved. The native Link closes all six pure fields and the one native body field without a supplied implementation premise.

Independent validation passed:

- Fresh native build: 934 jobs.
- Strict audit: all 69 physical-origin declarations in the six modules, with private lookup, recursive types, opaque bodies and constructors; only propext, Classical.choice and Quot.sound, no unsafe/partial dependency, zero exclusions.
- Seven executable actual-program smoke checks on MycpuBareWitness.entry, patched only at mstatus. The three nominal MPP cases preserve nonzero saved ELP/reserved bits; the base case returns the expected status view; the SIE=1 case outside the native disabled scope returns the old x15 view while clearing MS.SIE; fuel 0 and 2 return none. Every successful run checks Retire_Success, mstatus, x15, SP, TP and nextPC. These use ordinary #eval with IO failure on a false check; they are **executable smoke tests, not kernel proof certificates**.
- A separate compact exact-program factor was kernel checked, preserving the original nested write Result and all CSR read/write events. It adds no production assumption.
- All six frozen file lengths and hashes match the author's receipt and the hashes recorded before independent review.

Evidence under /tmp/xv6-lean-research: PushOffCsrPeerAudit.lean and push-off-csr-peer-{build,audit}.log; PushOffCsrExecutableChecks.lean and push-off-csr-peer-executable-checks.log; PushOffCsrCompactFactor.lean and push-off-csr-peer-compact-factor.log; push-off-csr-peer-results.json and push-off-csr-freeze.json. Final STATUS/design were read and agree with the native scope. The original raw Eq.refl fixture runs and a compact replay were stopped for cost without a result; compact cbv probes hit an isDefEq heartbeat limit. None is counted as a passing kernel certificate. The production generic actual-program/native proofs and strict audit supply the kernel evidence.

This is a same-hart, already-disabled normalized execution body rule. It does not establish fetch, decode, retirement, a full cycle/function, the enabled-to-disabled ghost transition, interrupt-count updates, migration or source-capability initialization. No stack-size lower bound is needed. The real continuation after Retire_Success is the public WP continuation, not a successful-execution oracle.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
