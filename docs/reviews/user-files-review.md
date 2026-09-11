# Independent filesystem user-file review

Codex coordinator review: PASS for the full-file content correspondence. Reviewed
`FileBytes{Defs,Proofs}`, `UserFiles{Proofs,Image}`, the complete producer
`tools/user_files.py`, and the generated certificate schema against pinned
`FsTree.v:605–614` and `FsImg.v:622–760`.

The generic ordered block reduction agrees with the source byte-by-byte reader,
including zero-filled holes and exact EOF truncation. Each concrete copied range
is proved from arithmetic slices of independently represented disk and ELF pages;
the proof then uses actual inode/direct/indirect readers and assembles every file
byte. The final four statements join raw-hex decoding, the checked root path,
and an actual filesystem-tree node containing the complete ELF file.

The producer checks the immutable source revision and source Git blobs, independent
file sizes/hashes, the full disk hash, actual inode type/size and W3 inputs. Its
emitted arithmetic and encoding claims are untrusted Lean inputs. The four files
contain 164,824 bytes, including DWARF and partial final blocks. Producer rejection
checks cover source/output corruption, truncation, final ELF and disk bytes; EOF
padding is deliberately excluded. The checked source schema uses separate full
hex/packed certificates, so equality of only host-generated packed values cannot
serve as the headline result.

The 339-job target build and 1,228 theorem-cone audit passed. Whole-project
physical-origin and implementation/statement audits remain part of integration.
Loaded program headers/code/data correspondence and user-program execution are
separate obligations, explicitly absent from this result.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
