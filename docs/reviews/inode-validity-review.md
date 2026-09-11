# Independent review: inode validity

Reviewer: Codex coordinator, independent of the implementing subagent.
Reviewed the complete `InodeValidityDefs`, `InodeValidityProofs` and separate
`InodeImage` leaf against pinned `iris/FsImg.v:684–751,962–1311`.

The definitions retain all nine source W3 fields, including zero unused direct
and indirect entries. The W3 sweep skips type-zero records. Full-region checks
retain the separate tail, link-count and bare-record obligations, including the
rounded records beyond the advertised inode count. Signed superblock fields,
Z.to_nat empty enumeration, modulo32 inode indices, and total zero defaults are
preserved. The stronger bare-address result is justified at out-of-list indices
by the actual zero default; it does not assume thirteen addresses on arbitrary
records. The block-coverage proof follows the source direct/indirect split.

The concrete leaf proves the actual live list1–22 and tail records200–207 free;
it does not turn those two checks into a full W3 or filesystem validity claim.
The source's1–24 comment is stale and is explicitly documented. Pure modules
remain independent of the image leaf. Regression proofs distinguish skipped
free records from the separate nlink/bare conditions.

The first fresh build encountered a transient syntax/depth failure in newly
added regression proofs; this was reported to the owner, who corrected it before
handoff. The final `python3 tools/lake.py build Xv6.Fs.InodeImage` passed219 jobs,
including the enforced audit of185 imported filesystem theorem cones.

Review result: the definitions and theorem contracts match the declared slice.
Whole-image inode validity, unique blocks, bitmap and directory/tree checks,
resource initialization and crash consistency remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
