# Four-byte datum bridge: independent complete review

PASS. Reviewed by `/root/lean_logic_audit` (OpenAI Codex), independently
of the coordinator who authored the five modules. I read all of
KernelDatumWord4Defs/Spec/Pure/Proofs/Link, the STATUS and boundary design,
and compared the definitions with pinned TsoCtx.v:628–641, 1061–1169,
CpuOwn.v:1–112 and the existing native KernelDatum/CpuOwn definitions.

The four virtual bytes retain the actual per-byte map claim, positive
virtual address, RAM condition, original tier pin, fractional physical
byte and timestamp/context resources. The identity-tier predicate agrees
with CpuOwn.word4 by kernel-checked reflexivity. General-tier access does
not assume identity mapping. Alignment proves same-page and no-wrap
geometry for each of the four modular offsets; there is no added global
address bound. The PPN is selected from an owned byte, and native map
agreement derives the common PPN for every other byte.

The access proof separates four persistent claims from the actual physical
window. Its replacement-value wand is constructed using those claims and
requires the replacement physical ownership at the original fraction and
context. It neither duplicates physical ownership nor fixes the old value
or timestamp. Closing restores all four virtual bytes at the original tier.
The native Link supplies every resource contract and the four geometry
laws without an accessor or consistency premise.

Independent target rebuild passed (660 jobs); all five source hashes
remained unchanged across the review. Fresh independent strict audit passed for **48 physical declarations in
five modules**, traversing all declaration types, opaque bodies and
constructors: only propext, Classical.choice and Quot.sound, no unsafe or
partial dependency, zero exclusions. The owner’s seven kernel examples
were independently replayed successfully, including CpuOwn equality,
page-end/max-address geometry and nonidentity physical mapping. Evidence:
`/tmp/xv6-lean-research/KernelDatumWord4PeerAudit.lean`,
`kernel-datum-word4-peer-audit.log`, `kernel-datum-word4-peer-checks.log`
and `kernel-datum-word4-peer.sha256`.

No correction requested. This is a native resource bridge; it does not
claim translation, a load/store event, noff/intena updates, or a function WP.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
