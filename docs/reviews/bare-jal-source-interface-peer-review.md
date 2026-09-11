# Bare JAL source interface peer review

PASS for the six-module Defs/Spec checkpoint. I am the separate
`lean_logic_audit` agent. I read all six BareJalFetch/BareJal/BareJalSource
declaration modules and the complete `bare-jal-source-boundary.md` design.
This is a signature and feasibility review, not a proof audit or a claim
that the proposed specification structures are already inhabited. The
owner reports the compiled checkpoint green at605 jobs.

I compared the interfaces with actual generated Fetch.lean216–273,
KptFetch's full factor/Plan/parts/chunks, SupervisorBare.Config and
SupervisorBareFetch's actual program/footprint/native read contract and
OneRead prefix implementation, the existing KptJal cycle contracts, source
WpSconfCtl237–281 and SRegime823–861. Existing source packet, physical-word
and context adapters were previously reviewed and are reused explicitly.

The nine fetch cells are exactly PC/MISA plus status, current privilege,
SATP, PMA regions, PMP configuration/address vectors and HTIF. Instruction
access ignores MPRV. The actual Bare prefix needs Supervisor/SXL and SATP
mode zero; it does not read MENVCFG or TLB. These facts are appropriately
separate from the broader control configuration required by actual active
execution and retirement. KptJal's generic decoder/body plans can use the
same fifty-cell packet without a new decoder normalization.

The three translation cells come from actual existential Bare ownership.
The partition patches only their values, joins them to the original fifty
cells and exposes nine fetch cells plus the filtered forty-four-cell
remainder, native bit ties and x0 fact. The unowned original control-file
SATP/PMP projections are not claimed to be physical state. Source closing
retains the actual Bare slot, so it needs no extra pure assertion about
those synthetic projections. No TLB cell is introduced.

`code` is the existing identity-tier F_Base InstrBytes assertion, including
actual four-byte RX/pristine ownership, two-alignment and non-RVC
classification. The reused outer Plan's parts can handle arbitrary words;
the public code assertion supplies the non-RVC fact when selecting the
one-four-byte or two-two-byte path. The split fetch retains both addresses
and read order, including offset4094 across a page boundary. There is no
word-alignment or same-page restriction hidden in the full-fetch contract.
The chunk theorem's supported width, alignment and text membership suffice
for the actual boot-PMA/TOR RAM obligations. Identity virtual window
ownership supplies physical/context bytes with their native timestamps;
no caller supplies a physical word or successful-read fact.

The guard fold contributes one later and a universally quantified view per
actual ordinary read, in order. Returned view receipts remain explicit.
Fetch and active preserve the separately framed reservation; the actual
restart boundary clears it. The cycle continuation quantifies every
Completed successor and next clock choice. Pure Plan/OneRead contracts
describe internal implementation obligations; none is an oracle premise
to the public source rule. The eventual native implementation must prove
these obligations and close the actual error/event cases before claiming
native closure.

The source input is the literal opened identity/Bare arm, not merely an
identity-tier capability. Native ownership and ambient facts derive the
needed control configuration, with same-hart boot-PMA explicit and retained.
The entire original virtual stack, timer, identity witness, hardware,
pending/stvec and caller frame remain in `kept`; no n≥2 premise is required
because JAL changes neither SP nor stack contents. The final source rule
returns the unopened capability at target with x1=PC+4, retained code/PMA
and frame, and only the genuine next-cycle continuation as its WP input.

No changes requested. General-PMA behavior, enabled-SIE migration,
unopened caller dispatch and entry/boot inhabitation remain separate, as
the design states. Full implementation review and strict physical/type/
opaque-body/constructor audits are still required after proof completion.

## Final native implementation review

PASS for the complete 22-module implementation: BareJalFetch eight modules,
BareJal eight modules and BareJalSource six modules. This additional review
was performed by the separate `lean_logic_audit` agent; `sail_audit`
implemented the modules. The preceding six-module interface review is
retained as historical signature-only scope. This section records the
subsequent full implementation review and native dependency discharge.

I read all 22 actual declaration, resource, factor, plan, native proof and
Link files, together with the final STATUS files and design. The actual
nine-plus-forty-four register partition obtains SATP/PMP values from the
existential Bare slot and patches only those three fields. It frames the
remaining physical cells, mstatus bit ties and x0, and restores their
ownership without treating unowned symbolic projections as physical facts.

The fetch folds retain actual one-four-byte or two-two-byte reads,
including a page-crossing second half. Each actual read contributes its
own guard and universally selected-view receipt; pristine/context byte
ownership pays the real native read. The decoder and JAL body reuse their
checked generated plans. Active execution retains the real dispatch,
default nextPC and successful retirement path, followed by actual clock
successors and the guarded restart with universally quantified next tick.
Reservations are framed through ordinary fetch and cleared at restart.
There is no supplied successful decoder, body, memory or cycle WP premise.

The source adapter derives configuration from the actual opened
identity/Bare arm and owned same-hart boot-PMA cell. The full original
stack and all timer, tier witness, hardware, slot and caller resources are
retained and returned. No stack minimum is added. The final actual source
capability is unopened at the computed JAL target, with x1=PC+4 and the
same code/PMA/frame resources. The only public WP input is its genuine
returned-cycle continuation. This establishes native closure for the
stated disabled-SIE, identity/Bare, boot-PMA specialization; it does not
establish source entry allocation, boot reachability, enabled-SIE behavior
or arbitrary-PMA support.

Independent validation completed successfully: a 1,196-job target build,
a fresh audit of all 204 physical-origin declarations across all 22 modules,
and independent replay of all 31 edge fixtures. The audit traverses
all types, opaque theorem bodies and constructors; only propext,
Classical.choice and Quot.sound occur, with no unsafe/partial dependency
and zero exclusions. All frozen source-file hashes remained unchanged.
No code corrections were requested.

Evidence under `/tmp/xv6-lean-research`: `BareJalPeerAudit.lean`,
`bare-jal-peer-audit.log`, `bare-jal-peer-build.log`,
`bare-jal-peer-checks.log`, `BareJalChecks.lean` and `bare-jal-peer.sha256`.
The complete review addendum was restored after the integration Markdown
normalizer accidentally truncated it at the earlier attribution note;
the audit/build/fixture evidence and unchanged 22-file hashes were retained.
A single standing attribution follows both review stages.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
