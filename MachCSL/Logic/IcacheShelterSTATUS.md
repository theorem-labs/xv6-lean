# Native inode claim and freeze shelters

The four `IcacheShelter{Defs,Spec,Proofs,Link}` modules implement the exact
native shelter and claim-pin definitions from pinned `InodeRegion.v`, using
the existing type and transaction cameras. The approved boundary is
`docs/design/icache-shelter-boundary.md`.

| Source | Lean implementation |
| --- | --- |
| `InodeRegion.v:1821–1837` | `ireg_fpin`, `ireg_fsh`, native transaction share and indexed boot/runtime regime, Timeless instances |
| `1839–1853` | Off introduction, pre introduction, exact post regime/pin return |
| `1860–1873` | `ireg_fsh_no_ops`, with the exact source `ireg_frz_ok` premise and actual empty transaction authority |
| `1882–1905` | Boot-token exclusion without an extra pure premise; same-index phase transport or affine off-target branch |
| `2564–2588` | `cty_pin`, `ireg_cpin`, exact optional pin extraction, none/some and native raw-element bridge |
| `2596–2607` | Claim no-ops with the exact source `ireg_claim_ok` premise |
| `2613–2630` | Paired `ireg_shp`, Timeless, intro/split/none laws |

All raw source cases remain represented. A live claim extracts its exact
transaction/share pair. An absent or invalid exclusive claim extracts none;
therefore `ireg_cpin_no_ops` retains the source pure claim-validity premise
to reject the invalid case. An absent or invalid freeze cell owns the source
`ireg_open ∨ ireg_boot` disjunction. It is not replaced by True, False or a
pure tag. Only the off freeze cell has the source True shelter.

Both pre and post own the actual `ireg_regime` at the Boolean index and the
actual `LogTx.tx_pin` at the exact transaction and positive share. The false
regime is the exclusive boot token and the true regime is persistent open
ownership. These fields are not hidden by new existentials. The post accessor
returns precisely the same full index, while the checked pre/post equivalence
and phase theorem preserve it. `ireg_fsh_step` retains the exact source
premise: target off or equality of the complete `frz_reg`. The source's
affine target-off branch discards its input; no pin-return claim is made for
that branch.

The freeze no-ops proof uses real transaction authority/fragment exclusion
for pre/post and the source pure freeze predicate for raw absent/invalid
cells. The claim no-ops proof uses native optional-pin emptiness and the
source pure claim predicate. The boot-off proof instead uses actual one-shot
exclusivity against either regime and both malformed disjunction cases; it
requires no additional pure freeze-validity premise.

Generic laws take explicit native type and transaction capacities and separate
boot and transaction-map ghost names. `nativeSpec` uses `LogTx.typeCapacity`
and `LogTx.registryCapacity` in the same existing registry. There is no new
slot, name allocation, new world, complete ambient icfg/log record, or initial
snapshot construction. The paired shelter retains both independently parked
shares when claim and freeze pins coexist.

Validation: `python3 tools/lake.py build MachCSL.Logic.IcacheShelterLink`
passes 474 jobs. The public API and private helper are covered by
`/tmp/xv6-lean-research/IcacheShelterOwnerAudit.lean`, which audits every
physical-origin logical declaration and all type, opaque-body and datatype
constructor dependencies. All 48 logical declarations pass with only
`propext`, `Classical.choice`, and `Quot.sound`; zero roots are excluded and
no unsafe/partial or `FsDurSnapshot.Initial` dependency occurs. The prefix
contains 23 named theorems (including one private helper) and four Timeless
instances.

This completes the listed native shelter dependency, not the full inode-slot
invariant, physical counter/record updates, epoch receipt, escrow registry,
ticket/corpse resources or complete log/commit execution. The no-ops rules
require actual empty transaction authority and their exact source validity
premises; those facts are not assumed globally. Full source claim/freeze
mint, withdrawal, and invariant-opening protocols remain separate dependent
work. No transaction-pin or index oracle is introduced.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
