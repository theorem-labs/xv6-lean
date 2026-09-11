# EventPlan mode-eligibility correction

Author: OpenAI Codex subagent `lean_logic_audit`, implementing the approved
correction after designing concrete lock callbacks. This records an interface
finding and its disposition, rather than claiming an independent review of
my own implementation.

The original `WriteAccess` required every `WriteMode` for each enabled request.
For a protocol index recording a preceding read of zero, this included ordinary
mode, whose `WriteFact` is only `True`. The callback could not establish that
the physical lock was still zero: the exact reservation fragment is correctly
carried separately by the fold and must not be duplicated into its protocol
resource. The actual conditional-write plan has the needed reserved-mode fact,
but the callback contract also required an unused, stronger ordinary-mode case.

The approved correction adds `Relations.writeModeEnabled`, indexed by the
protocol state, reservation, size, complete request, value and chosen mode.
`Plan.write` proves both request eligibility and mode eligibility; `WriteAccess`
is required only for those eligible modes. The native fold passes that proof
to the resource callback and uses the same native ordinary/conditional rule
as before. No machine guard, request field, result, blocked case or successor
is added or removed. The conditional mode still requires the exact snapshot
and its strict extraction bound; ordinary mode retains the general-width rule.

Concrete AMO plans select reserved mode at their actual conditional-write
boundary. Ordinary counter stores and unlock stores select ordinary mode.
The relation's eligibility witnesses are proof-rule selection constraints,
not assumptions that successful hardware writes are the only possible steps.
The native leaf rules still prove all blocked and successful successors.

The corrected six-module target builds in 470 dependency jobs. Its fresh
physical-origin/type/body/constructor-cone audit is recorded in
`EventPlanSTATUS.md`; no custom axioms or unsafe/partial dependencies are
introduced. The coordinator approved this correction before edits; the
independent actual-access-plan owner coordinated the additional constructor
argument. The existing fold review should be read together with this change.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
