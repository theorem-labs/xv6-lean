# Blockwise file-byte reduction

`FileBytesDefs.takeBlocks` is source FsImg.v620's ordered block concatenation.
`FileBytesProofs` proves its length and byte lookup, exact prefix equality with
`FsTree.file_bytes`, and `node_at_file` for every nonzero non-directory type.
It reuses the existing `BlocksFull`/`dataOf_sized`; sparse holes keep their source
zero-fill behavior. No concrete image imports occur in these generic proofs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
