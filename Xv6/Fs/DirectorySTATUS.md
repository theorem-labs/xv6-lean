# W6, W7 and W8 directory checks

`DirectoryDefs`, `DirectorySpec` and `DirectoryProofs` port the exact pure
checks at pinned `iris/FsImg.v:1919–2274`, using the previously proved
Dirent/DirView/FsTree byte and first-match foundation.

`dirUniqb` builds the native finite name set in source index order. Free
entries leave the set unchanged; a repeated canonical name of a live record
causes `none`. Successful collection has exactly the live-record names,
success is equivalent to `DirNamesUnique`, and failure to its negation.

W6 `dirValid` checks 16-byte size divisibility, every live entry's positive
target below `ninodes`, target-inode liveness, canonical-name uniqueness,
first matching dot naming self, and existence of first matching dotdot.
`DirectoryOK` has the five original fields, including actual `dirView`
lookups. The Boolean and Prop are proved equivalent. The complete advertised
inode sweep checks precisely type1 directories; negative counts remain
empty. The region-inum coverage projection uses an explicit region bound.

W7 `rootValid` checks that inode1 has directory type and its first matching
dotdot names inode1. W8 remains a separate check: it requires at least two
records, live self-dot at index0, and live dotdot at index1. The source
`DirDotsIx` implication guards are retained in its Prop projection.
W6 does not imply W8. A kernel regression accepts swapped dot records under
W6 and W7, but rejects them under W8. Other regressions reject dead targets
and duplicate live names while accepting duplicate garbage names in free
records.

Validation:

```sh
python3 tools/lake.py build Xv6.Fs.DirectoryProofs
```

The 14-job build passes, with the proof module taking about one second.
All 262 imported filesystem/directory theorem cones are checked against
the standard three-axiom allowlist. No native evaluator, `bv_decide`,
`sorry` or custom axiom is used. These generic files import no image.

Concrete directory certificates, W9 ticket/link checks and the full initial
`fsimg_wf` composition are the next leaves. Path/tree-node representation and
mutation proofs remain subsequent ports. The source's later durable DWF,
`links_eq` and `root_no_self` checks remain separate predicates; they will
not be silently included in or substituted for the original initial checker.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*

Concrete image closure: `DirectoryData` checks all 1024 bytes of actual block47
against the pinned raw-image input and proves the full `dataOf` function equality.
`DirectoryImage` checks the exact sole-directory enumeration `[1]`, W6 entry
bounds and actual target liveness, unique names, dot/dotdot, W7 root, and W8
physical dot indices. All free entries and padding remain in the literal input.
The final target builds234jobs; leaf8.9seconds. Its enforced audit covers437
filesystem and imported inode certificate theorem cones, standard three axioms only.
Regenerate with `python3 tools/directory_certificates.py .upstream/xv6iris`; verify reproducibility
and source-pin rejection paths with `--check --self-test`.
