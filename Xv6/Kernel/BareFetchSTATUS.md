# General Bare instruction fetch

FROZEN native implementation: the public fetch contract is implemented in
four modules. Build1067 jobs; strict audit24 physical/private/type/opaque/
constructor declarations, standard three axioms, zero exclusions and no
unsafe/partial dependency. Eleven kernel geometry/classification checks
pass: aligned/unaligned compressed/base reads, cross-page half reads and
actual selected chunk widths. Full independent implementation review passed, with fresh build/audit,
fixture replay and unchanged frozen hashes.

The old generic BareJalFetch.fold and fetch_plan are reused without edits.
KptFetch.select_word extracts the actual byte-backed classification and
windows, so F_Base and F_RVC share the actual outer fetch program. Aligned
compressed instructions retain the four-byte fetch footprint; unaligned
compressed instructions read one halfword. Base instructions at PC mod4=2
read two ordered halves, including page crossing. The code predicate
rejects error-result constructors; arbitrary successful classification does
not mint ownership. All9 register cells, running context, original code
and exact read receipts return. Reservations can be framed by callers.

Evidence: bare-fetch-link-build2.log, BareFetchOwnerAudit.lean,
bare-fetch-owner-audit.log, BareFetchChecks.lean, bare-fetch-checks2.log and
bare-fetch-freeze.json under /tmp/xv6-lean-research. No model, previously
frozen fetch proof, camera or umbrella was edited. Source packet composition,
decoding/body execution, full cycles/functions and whole-system roots remain
separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
