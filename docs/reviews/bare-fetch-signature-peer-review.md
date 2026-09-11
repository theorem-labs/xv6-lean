# BareFetch signature review

PASS for the two-file interface checkpoint, independently reviewed by Codex `artifact_audit` against root-authored `BareFetchDefs` and `BareFetchSpec`. No native implementation result is claimed by this signature review.

The contract extends the earlier F_Base-only BareJalFetch wrapper to both byte-backed successful fetch classifications. It reuses the exact same Config, footprint, cells, actual fetch program, read guards and view receipts. `KptFetch.instrBytes` at the identity tier supplies real discarded byte windows, instruction alignment and classification. Its error constructors are false, so quantification over FetchResult does not claim that error-result code resources are inhabited.

The proposed proof is supported by existing implemented interfaces: `KptFetch.select_word` returns the correctly classified finite word and actual chunk windows; `BareJalFetch.fetch_plan` already covers both classifications; `BareJalFetch.fold` performs the native reads; `KptFetch.parts_addresses` identifies the precise guard sequence. Four-aligned compressed instructions retain a four-byte owned window and one read; other compressed instructions need one halfword read; a non-four-aligned base instruction requires two ordered halfword reads. The pinned Ziccif query and Zca/MISA reads remain in the actual plan. No new alignment, memory-readability oracle, translation-success premise, camera or register duplication is introduced.

The actual code predicate is persistent, allowing it to remain in the post while the selected chunk windows are used. The same register cells and running context return with actual read receipts. Implementation and its full declaration audit are still separate from this checkpoint.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
