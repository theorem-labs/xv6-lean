# Actual disabled push_off CSR body

Native implementation GREEN: all six pure and one native contract in the
approved Spec are implemented across six modules. Link build:934 jobs,
no warnings. Strict physical/private/type/opaque/constructor audit:69
declarations, standard three axioms, no unsafe/partial dependency and zero
exclusions. Independent full implementation review/build/audit passed.
Seven executable actual-program smoke checks passed independently and on
owner replay. They check nominal MPP0/1/3 with saved ELP/reserved bits,
base status, SIE1 old-destination/new-status distinction outside the native
disabled rule, and fuel0/fuel2 rejection. Successful cases also check SP,
TP and nextPC. These #eval/IO-failure checks are not extra kernel proof
certificates. Production proofs and the separately checked compact exact
program factor remain ordinary kernel evidence. Slow raw/cbv fixture
attempts were stopped or timed out and count as no successful certificate.

nativePureSpec.plan proves actual execute on source row5 (CSRRCI sstatus,2,
a5), with full MS/x15 cells and fractional privilege/MISA. The real CSR
access check and both privilege reads remain. The first read returns old
lower_mstatus; the actual pre-write MS read, legalizer, physical identity MS
write and post-write MS read remain. x15 receives the old status. Under
MsFacts and SIE0 the legalizer returns precisely the old MS, including
arbitrary saved SPELP/MPELP bits. The native body obtains those facts from
the actual packet's same-name bit fractions, folds every register event,
and restores the complete same-regime packet, other GPRs and literal frame.
The generic legalizer is supplied internally through its native Link.

Owner evidence: PushOffCsrOwnerAudit.lean, push-off-csr-owner-audit.log,
push-off-csr-link-build.log, PushOffCsrExecutableChecks.lean and
push-off-csr-owner-executable-checks.log; the peer replay is
push-off-csr-peer-executable-checks.log and the compact exact factor is
PushOffCsrCompactFactor.lean
under /tmp/xv6-lean-research. Freeze receipt: push-off-csr-freeze.json.
Fetch/decode, retirement/cycles, source function restoration, initially
enabled behavior and all six whole-system roots remain outside this body.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
