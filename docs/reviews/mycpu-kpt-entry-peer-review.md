# MycpuKptEntry independent review

PASS for four pure and four native resource contracts. Read all five
complete modules; independent fresh full physical/type/opaque/constructor
audit checks all53 declarations, with standard axioms only, no unsafe/partial
dependencies and zero exclusions. Owner build966 jobs passed.

Input is the actual full-tier disabled source capability and pc_is at mycpu
entry, plus an actual same-hart discarded boot-PMA cell and native code.
The latter two additions remain explicit specialization/resources, rather
than conclusions from the general source hardware assertion. Opening uses
native register agreement for PMA, the one-bit ELP fact for no landing pad,
and full-tier kptOn to eliminate the Bare pending branch.

The actual virtual free stack at n≥2 splits into two arbitrary saved words
at immutable entrySP−8 and entrySP−16 plus its exact n−2 tail. No initial
RA/S0 equality is assumed for these scratch words. The returned packet owns
all50 cells, native residue at the source kptN/root, exact reservation,
running context, code and literal retained tail/timer/hardware/shot/kptOn resources.
Closing only needs returned SP=entrySP and the actual source Boundary at the
return PC. It rejoins arbitrary returned words with that same tail and
restores the complete original source capability and pc_is, retaining code
and boot-PMA resources. Certificate extraction retains the whole packet.

This is a resource adapter, with no instruction, successful execution or
function-WP premise. Actual boot allocation/entry reachability and full
function composition remain open. Evidence:
/tmp/xv6-lean-research/MycpuKptEntryRootAudit.lean and
mycpu-kpt-entry-root-audit.log.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
