# Calling-convention register preservation

Frozen four modules: CalleeSaved Defs/Spec/Proofs/Link. The preserved
registers are exactly source CalleeSaved.v:34–48: x2, x8, x9 and x18–27.
`preserved_iff` checks the explicit thirteen-conjunct spelling; TP is
excluded because a thread may migrate. `preserved_refl`, `preserved_trans`
and `caller_write` port the corresponding source laws.

The dependent typed `Write` list extends source GPR-only writes to every
actual Sail register. `applyWrites` folds right, with the outermost write
first. `applyWrites_lookup` and `applyWrites_preserved_iff` prove exactly
when the final write at each saved register restores its entry value;
`applyWrites_preserved` discharges the public Spec. This is pure register
bookkeeping, not a function or machine execution theorem.

Build: `python3 tools/lake.py build Xv6.Kernel.CalleeSavedLink`, 149 jobs.
Full owner and independent audit: 40 logical declarations, standard three
axioms; one identified safe-owner total-recursion compiler companion for
outerWrite excluded only as a root, forbidden in logical cones. All
opaque/type/constructor dependencies checked. Independent source review
passed: docs/reviews/callee-saved-peer-review.md. Evidence under
/tmp/xv6-lean-research/callee-saved-{build,audit}.log.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
