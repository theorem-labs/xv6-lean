# Exact filesystem replay

Stage 1 is frozen in six modules: Defs/Spec/Proofs/ViewProofs and separate
ExamplesDefs/ExamplesProofs. CodecSpec, InstallSpec and Spec are all
implemented by kernel-checked proofs: 27 public contract laws, supported
by ordered-fold helpers, with 43 named theorems including the ten fixture
facts and three completed specification instances.

Source: LogDefs43–67/155–164 and FsCrash349–366/460–480/640–810/844–940
at arxiv-v1 fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. The design and exact
Defs/Spec received coordinator review before proofs. Existing signed
SnapshotHome carriers/restriction are reused unchanged.

The decoder retains short headers and unbounded decoded counts. Ordered
replay retains first-index winner on duplicate writes. HeaderWF has
exactly the three source clauses, including block 1 exclusion inside the
per-entry clause. Fullness and misses need no header validity; hits retain
duplicate-freedom, and recovered-domain/view/slot facts use the stated
HeaderWF premises. Recovery is an equality to actual replay, not a new
oracle. Absent recovered keys fall back to raw bytes; the complete header
write set remains exceptional even when a payload already agrees.

Kernel fixtures check a one-byte header decoding one absent word as zero,
count 31 remaining 31, duplicate destination first-index behavior, a dirty
header replacing raw home contents, an equal-payload destination remaining
in the exception set, and raw fallback outside the home map. The dirty
and equal fixtures use full 1024-byte physical blocks and satisfy the
actual HeaderWF predicate. No native-decide or unchecked host assertion.

Validation: final `python3 tools/lake.py build
Xv6.Fs.RecoveryExamplesProofs` passed **38 jobs**, with no warnings in the
new modules. Final fixture compilation took 516ms. The full physical-origin
audit checked **128 logical declarations in all six modules**, including
private/generated roots, complete opaque bodies, types and datatype
constructors. Only propext/Classical.choice/Quot.sound occur; zero excluded
roots and no unsafe/partial or Initial allocator dependency. Evidence:
`/tmp/xv6-lean-research/RecoveryOwnerAudit.lean`,
`recovery-owner-audit.log`, and `recovery-examples-build.log`.

During implementation two type annotations were needed for list values
and signed literal keys. Fixture simplification initially unfolded a full
1024-byte replicate too eagerly; the final proof uses exact list length
and conditional laws, without increasing a trust boundary or changing
any definition. Generic native disk carve, byte mint and actual era
integration are subsequent approved-design stages and are not claimed
by this pure checkpoint. HeaderWF extraction from the future native P_fs
predicate remains distinct from initial clean-header discharge.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
