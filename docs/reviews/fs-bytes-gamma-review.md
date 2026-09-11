# Independent review of the logged filesystem byte bridge

Reviewer: the independent Codex `sail_audit` agent. Result: PASS.
Reviewed all three frozen Lean modules against the complete 127-line
`iris/FsBytesGamma.v` and `FsBlocks.v` lines69–91/341–396 at paper tag
`arxiv-v1`, commit `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
No production-file changes were made by the reviewer.

The six-field name carrier preserves cache, dirty, byte, link, top, and
exception names in source order. Names remain parameters rather than
assumed ownership. The concrete byte predicates use signed Int keys and
native ghost-map elements at the existing disk-image camera; byte ranges
preserve stride1024, signed offsets, list-index addition, arbitrary byte
lists, and arbitrary DFrac. Full-block predicates add exactly length1024.

The logged view uses the byte, link, and top names from this carrier.
Its full and fractional byte/block conversions match the source by
conversion. Exclusivity is the exact joined-fraction validity law, not
an assertion that every pair of fragments is invalid. Fractional splitting
and timelessness come from the same native ghost map. The extra
`snapGamma` equality and `PhiAgree` witness are valid consequences of this
concrete view; agreement needs the matching native map authority.
The bridge makes no claim that its map equals live disk, cache, or RAM,
and performs no allocation. The registry projection correctly identifies
Disk slot12. Omitting unused source section typeclass parameters from
these generic Lean laws does not strengthen their resource premises.

Independent verification:

- `python3 tools/lake.py build MachCSL.Logic.FsBytesGammaProofs` passed
  405 jobs from the frozen sources.
- `/tmp/xv6-lean-research/FsBytesGammaIndependentAudit.lean` checked every
  one of the 40 physical-origin declarations, including private/generated
  helpers, through transitive types, opaque/theorem bodies with
  `allowOpaque := true`, and referenced constructors. Only `propext`,
  `Classical.choice`, and `Quot.sound` occur; no unsafe or partial semantic
  dependency, zero exclusions. Its additional Initial-prefix dependency
  rejection also passes.

Frozen source SHA256 values:

| File | SHA256 |
| --- | --- |
| FsBlocksBytesDefs.lean | 6fa977d2da0b676ff61a2d1429060aadc3d80b824b8d27a4a497e393fa109de8 |
| FsBytesGammaDefs.lean | 5473b0263ad46aee68cbfa402faebcf9dca0456f891bd50f8eba4fd4a355a161 |
| FsBytesGammaProofs.lean | 036902527ba0e60ca8c6e8b7afd9ccb4f0bf0e01b18160d6770d2fcac31567c5 |

This approval covers the byte-view bridge and its stated laws. Cache/log
invariants, their byte-value coupling, and allocation remain separate.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
