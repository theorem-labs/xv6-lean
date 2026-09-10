# Generated paper RISC-V model

This package contains the 87-module import closure of the paper's generated Lean
RISC-V model, using the free V1 runtime at `28c729b5`. The module prefix
`LeanPaperStock` preserves the original generator output name; its monad is the
opt-in free event monad, not the sequential stock interpreter.

`Platform` contains only the paper's two arbitrary but fixed reservation
predicates. Reservation updates and terminal output are the paper's pure noops;
experimental extensions are disabled by its exact `false` hook. The unsupported
pure and effectful externs are separate parameter classes, with no implementations.
The compiled entry-point audit rejects dependencies on either class. It also
rejects custom axioms, partial/unsafe implementations, execution overrides, opaque
data, the free choice primitive, and any import of `FakeReal`.

The original raw generation is recorded in
[`docs/upstream/sail-generation.json`](../../docs/upstream/sail-generation.json).
[`provenance.json`](provenance.json) records this package's source hashes,
runtime pin, adapter hashes, module closure, and platform bindings. Rebuild and
regeneration instructions are in [`docs/Sail-generation.md`](../../docs/Sail-generation.md).
Generated files must be regenerated through the recorded adapters, not hand-edited.

The register reads nested inside `print_rvfi_exec` are named explicitly to avoid
costly elaboration. Their order and pure helper calls are retained; the local
bind/pure normalization identity is kernel checked. Removing 28 unused `FakeReal`
imports leaves no approximated real-arithmetic helper in this package.

```sh
lake update
LEAN_NUM_THREADS=2 lake build
LEAN_NUM_THREADS=2 lake env lean Tests/ModelAudit.lean
LEAN_NUM_THREADS=2 lake env lean Tests/RootJal.lean
LEAN_NUM_THREADS=2 lake env lean Tests/NormalizationProofs.lean
```

The JAL test proves the actual generated instruction's four-event register trace
and final next-PC value under an explicit fixture. It does not establish fetching,
machine initialization, concurrency, device behavior, adequacy, or xv6 safety.
Cross-backend event correspondence remains a separate required proof.

Upstream Sail compiler and RISC-V model notices are preserved in `LICENSES`.
The pinned lean-sail library has no standalone upstream license file; this package
assigns no new terms to inherited library code.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
