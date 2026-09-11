# Complete slot numbering and entry list

`SlotsDefs` implements source FsImg.v1389–1418 and2879–2957: file slots0–267,
indirect-root slot268, a269-element list with the root first, and `runIndex`
reindexing. `inodeEntries` filters only zeros, retaining every other occurrence
regardless of file size. Arbitrary address lists retain total-zero lookup defaults.

`SlotsProofs` covers exact source index injectivity/surjectivity, list length,
lookup/member correspondence, record/view transport, durable block range,
nonzero-list duplicate freedom implying slot injectivity, and the source
single-slot update theorem. Filling one empty slot adds exactly one multiset
occurrence; the proof does not assume the new block is fresh or erase duplicates.
Kernel regressions reject an alias between direct slot0 and the indirect-root slot.
All theorem cones are subject to the standard-three axiom allowlist.

Source initial-size `fs_slot_pos` numbering is a separate later bridge; the
actual W4 slot-injectivity consequence is now supplied through ordered entry-list
correspondence in `DurableBlocksProofs`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
