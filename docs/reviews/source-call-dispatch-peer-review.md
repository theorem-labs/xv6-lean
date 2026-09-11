# Native source caller dispatch peer review

Reviewer: OpenAI Codex root agent, independent of the implementing logic agent.
Scope: all four JalSconf and all four MycpuCallSconf modules, including complete
proof bodies and native dependency discharge. Verdict: PASS for these exact
same-hart, interrupts-disabled, boot-PMA-specialized source contracts.

JalSconf opens the actual source capability once. Its Bare branch derives the
identity tier from admissibility, and its KPT branch retains either original
tier. Both invoke native actual-cycle rules. No caller-selected regime,
configuration, physical word, successful evaluator result or component WP is
an input to nativeSpec. An even target is explicit; code ownership supplies
alignment. No stack minimum is imposed on JAL. The restored capability has
x1=PC+4, target pc_is, the same scratch count, code, PMA and caller frame.

MycpuCallSconf composes that JAL with the native fourteen-cycle MycpuSconf
function. Its public preconditions require two available words and the actual
mycpu target. It preserves code/text/PMA and source tier, proves the return
address has clear low bit, restores source pc_is at PC+4, and transfers the
saved-register and entry-TP result from the actual function theorem. Its only
WP input is the genuine final continuation.

Validation: the implementing agent's combined 1,276-job build passed. Root
read every module and ran separate physical-origin audits over the actual
environment, traversing declaration types, private/opaque implementation
values and constructors with exporting disabled. JalSconf checks 20 and
MycpuCallSconf 19 declarations. Both permit only propext, Classical.choice
and Quot.sound, reject unsafe/partial dependencies, and add zero exclusions.
Drivers and logs are /tmp/xv6-lean-research/JalSconfRootAudit.lean,
JalSconf-root-audit.log, MycpuCallSconfRootAudit.lean and
MycpuCallSconf-root-audit.log. The separately implemented 22-module Bare JAL
branch has its own complete independent logic-agent review; this report does
not claim root reread all of those files. Fable round 12 predates this scope.

Boot/source entry inhabitation, enabled/migrating callers, arbitrary platform
PMA, complete push_off and all six whole-system roots remain open.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
