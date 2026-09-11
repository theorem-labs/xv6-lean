# Native pinned conditional-write independent review

PASS for the direct conditional RAM event and generated write_ram wrapper.
Root reviewed all four physical modules, STATUS, the full design and the
existing native conditional-event and reservation interfaces.

The payer constructs its modular address-to-offset map internally and
applies the native pinned store to the actual writeState. It updates the
complete heap metadata/byte/timestamp/log/view interpretation and frames
register/device authorities. The returned pin timestamps and receipt index
have the exact one-based/zero-based relationship and positive time.

The held-word agreement lemma combines actual heap readback with actual
snapshot validity. Its resource-preserving version retains all authority
and client resources. No pairwise reservation disjointness follows or is
assumed. The actual event theorem retains blocked unchanged writes and
successful commits, with source reservation clearing and exclusive view
advance. The generated all-response equation maps Ok to true and Err to
false; only the native event semantics rules out a completed Err response.
No hardware success bit, fairness or eventual-commit assumption is added.

The main write proof receives the held snapshot's real readback from the
native conditional rule. Its allowed-byte payer needs only the full newly
opened physical slot and membership, so it does not assume physical and
reserved values equal as an extra premise. Their equality is independently
derivable by the exported agreement rule. Checked supervisor prefixes and
shared KPT accessor construction remain later obligations.

Fresh root audit passed all **75 logical declarations** in four physical
modules, including complete transitive types, opaque bodies and datatype
constructors. Standard three axioms only; zero exclusions, no unsafe or
partial logical dependencies. Evidence:
`/tmp/xv6-lean-research/TsoPinnedWriteWPPeerAudit.lean`,
`tso-pinned-write-wp-peer-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
