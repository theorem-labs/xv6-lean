# Mycpu fixed-anchor decoded bodies

FROZEN: all thirteen pure contracts and the native body contract are
proved in five modules (Defs, Spec, Pure, Proofs, Link). `nativePureSpec`,
`nativeSpec` and `registrySpec` are actual constructors. The approved
Defs/Spec signatures are unchanged.

The route covers all fourteen actual decoded execute/ExecuteAs bodies:
nine scalar instructions, four stack memory instructions and the final
compressed return. It reuses the existing fifty-cell packet and folded KPT
residue. The save-area anchor is always entrySP−16, with RA at anchor+8 and
S0 at anchor. Scalar SP changes preserve these literal addresses. Memory
bodies alone require the actual current SP to equal the anchor.

The contract computes the resulting control file, pinned GPR map and saved
words from the indexed body. Register outcomes retain the reservation;
memory outcomes carry the actual translation result, reservation update and
receipts. The continuation preserves the existing translation/A-D guards
followed by exactly one data-event guard. Raw false/error tail equalities
remain explicit. No successful-body WP, physical-word input or translation
success premise is introduced.

The phase-SP helpers provide indexed bookkeeping, not a completed function
phase invariant. Actual fetch, decoder dispatch, retirement, restart and
full source function/sconf composition remain separate obligations.

Validation: `python3 tools/lake.py build Xv6.Kernel.MycpuKptBodyLink` passed
1,066 jobs (Pure 1.6 s, Proofs 1.4 s, Link 1.1 s). The final build log is
`/tmp/xv6-lean-research/mycpu-kpt-body-build6.log`. Fresh full physical-origin
audit checked all 178 declarations in five modules, traversing every type,
opaque value and constructor dependency: only propext, Classical.choice and
Quot.sound; no unsafe/partial dependency and zero exclusions. Audit script
and log are `MycpuKptBodyAudit.lean` and `mycpu-kpt-body-audit.log` under the
same research directory. Source mapping and exact scope
are in `docs/design/mycpu-kpt-body-boundary.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
