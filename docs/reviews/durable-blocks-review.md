# Independent review: slots and durable allocated blocks

Reviewer: Codex coordinator. Read all Slots and DurableBlocks modules and
actual-image leaves; compared source slot1390, entry-list2763–3324 and W3
ordered-list correspondence definitions and arguments.

The exact 269-slot numbering includes the indirect-root slot268, mapped to
list position zero. Direct and indirect data follow in source order. The
nonzero filter preserves duplicates and therefore counts every owned entry,
including allocations beyond size. Its injectivity proof rules out aliases
between data and the indirect root. Updating an empty slot adds precisely one
occurrence under permutation, with explicit unchanged-other-slot premises.

The W3 bridge requires SuperblockOK and InodeOK. It uses positive data-start
and the original zero-suffix/coverage clauses to prove equality of ordered
lists, not just sets. The whole-image bridge preserves inode ordering and
skips only free records. Global NoDup yields per-inode injectivity and
cross-inode disjointness with explicit bounded/live/distinct premises.

Actual image results reuse the complete checked bitmap and W3 readers through
these general equalities; no second untrusted image calculation is accepted.
Review: PASS. Initial-size slot-position and higher tree/resource projections
remain separate, documented proof obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
