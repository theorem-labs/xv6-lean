# Independent user ELF files inside the filesystem

The four inputs are the complete pinned `user-rocq/{Echo,Init,Sh,Sync}ElfRaw.v`
blobs, including ELF headers, non-loaded sections and DWARF. They are imported
independently from the filesystem bytes. Sizes are35592,35976,58312,34944 bytes;
SHA256 and source-blob SHA256 are recorded in every generated module.

`tools/user_files.py` verifies the repository pin, each working raw source against
its pinned Git blob, file and disk sizes/hashes, original inode size/type/W3,
and exact file-byte/disk agreement before emitting untrusted inputs. Existing
`tools/images.py` is read only for strict extraction and balanced-expression
helpers. `Generated/User/*Encoding*` independently kernel-checks every hex byte
against its packed counterpart using the existing shared one-byte certificates.

`UserFilesProofs` derives a byte window equality from two independent arithmetic
page-slice certificates, lifts the equality through the actual disk/block/indirect
readers, then assembles full file content. Generated disk certificates use all
actual W3 record and indirect-entry equalities. All1024-byte block boundaries and
4096-byte page boundaries are respected, including each final partial block.
`UserFilesImage` joins exact root paths, node contents, and raw-hex decoding.

Reproduce and run rejection checks:
`python3 tools/user_files.py .upstream/xv6iris --check --self-test`.
The checks reject a truncated ELF, changed final ELF byte, and changed final disk
file byte; changing the unread padding immediately after EOF leaves the file
certificate unchanged. Every generated theorem cone is audited in the final leaf.

These are full-file content equalities. ELF program-header parsing, loaded-code
and data-map correspondence, and user-program execution require their separate
proofs; none follows merely from a path lookup or file-content equality.



Validation checkpoint: full target `Xv6.Fs.UserFilesImage` passed339jobs. The
42 hex-page certificates cost roughly16seconds per full page (two jobs at once);
all four complete disk-copy certificate modules cost1.2–1.8seconds each. Final
headline/audit leaf1.1seconds;1228 Fs/private/user-ELF/inode theorem cones checked,
with only `propext`, `Classical.choice`, and `Quot.sound` allowed. Full independent
file contents total164824bytes. The producer's `--check --self-test` passed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
