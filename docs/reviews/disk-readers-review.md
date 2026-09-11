# Independent direct filesystem reader review

PASS for the four generic normalization theorems and the current concrete
`region_nlink_checked`, `region_bare_checked`, and `region_valid_checked` theorems. All7 theorem cones were independently audited;
only propext, Classical.choice and Quot.sound occur.

The inode-window theorem retains modulo32 conversion of the inode index and
signed superblock block addresses. The bound offset+count≤64, combined with the
actual inode slot bound<16, proves every field access remains inside the same
1024-byte block. The reader uses exactly the original little-endian assembler.
The full dinode theorem preserves all scalar widths and13 address fields.
Indirect-entry normalization retains the optional13th-address default and the
zero-indirect-block branch; it neither reads a block when the source returns
256zero entries nor extends arbitrary short address lists.

Independent kernel checks exercise signed direct-byte addresses (reading four
bytes beginning at-2), a missing indirect pointer producing the complete zero
entry list, and inode-1 wrapping identically to2^32-1. The concrete region nlink
proof checks all208 records and retains the source's type-zero implication and
signed-short upper bound. The appended bare proof checks size and the entire
address list at every type-zero record across all208 records. The region-valid
proof combines exactly the already checked tail-free and nlink conditions; bare
remains separate. These do not certify W3.

Documentation: keep the module header scoped to rounded inode-region checks
until the separate W3 image certificate is complete.

Replay: `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py env lean /tmp/xv6-lean-research/DiskReadersIndependentAudit.lean`

SHA256:
Xv6/Fs/DiskReaders.lean cd6c23de926e3e2614fade62ae64dbca91c868671aee3408f280cad4db6141f8
Xv6/Fs/InodeCertificates.lean 723741b839f52fcfff111b5eb5d731e7f56dbea087005e13a9ac59bd913ab869

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
