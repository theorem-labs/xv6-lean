# Supervisor sstatus off normalization

Complete and frozen: Defs, Spec, Pure, Plan, Proofs and Link. All eleven
approved contracts are implemented by `nativeSpec`, with no supplied
component contract or evaluation-success premise.

The actual pinned `hartSupports Ext_Zicfilp` is true. The generated
legalizer uses support, not current MENVCFG.LPE; arbitrary saved SPELP and
MPELP bits are preserved. Under exact source `SupervisorBits.MsFacts` and
SIE=0, `legalize_sstatus ms (lower_mstatus ms &&& ~~~2)` returns exactly ms.
The result retains source MsFacts, SIE=0, and SPP/SPIE/SPELP/MPELP.

`legalize_plan` proves the actual generated `legalize_mstatus` for arbitrary
old/new words using a listed fractional MISA cell at the source full MISA
value. It retains repeated eager S/U/virtual-memory queries, all four MPP
encodings, and invalid-MPP User fallback. `off_plan` composes this with the
source bit normalization. The helper's status is an argument, so this
isolated program needs no mstatus, privilege or MENVCFG ownership. The
surrounding CSR instruction's actual reads/writes and native WP are separate.

Pure proofs use bit extensionality and an arbitrary-width slice-update
identity. Kernel regression certificates check nonzero saved ELP bits,
SUM, SPP/SPIE, MIE/MPIE, UXL=3, a reserved high bit, and all MPP outcomes.
No generated semantics, source status constraints or existing families
were changed. No memory event, reservation, camera or namespace is added.

Source correspondence: `WpGprCsrwCommon.v:240–301` supplies the symbolic
legalizer and masked S-view; `WpGprCsrwC.v:1362–1429,1675–1702` supplies
lower/lift/update identities and off normalization;
`WpSieFlipBits.v:289–345` gives the broader fact-preservation context.
Actual generated programs are `SysRegs.lean:676–688,1009–1090,1431–1466`
and the eager extension queries in `PlatformConfig.lean`. Full source
enabled-SIE flips, top CSR execution and whole push_off remain separate.

Validation:

- `PATH=/home/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Logic.SupervisorSstatusOffLink`: GREEN, 351 jobs. Pure took 3.3s; Plan 14s; final concrete Proofs 3.9s and Link 2.9s.
- Strict owner audit: all 606 physical declarations in six modules, including private/generated declarations and complete type/opaque-body/constructor dependency cones; only propext, Classical.choice and Quot.sound; no unsafe/partial dependency; zero exclusions.
- Audit driver `/tmp/xv6-lean-research/SupervisorSstatusOffOwnerAudit.lean`; build/audit logs `supervisor-sstatus-off-build.log` and `supervisor-sstatus-off-owner-audit.log`; exact source hashes in `supervisor-sstatus-off-frozen.json`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
