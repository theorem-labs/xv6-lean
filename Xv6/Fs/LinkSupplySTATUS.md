# Native link supply and counting

Source: `xv6iris` tag `arxiv-v1`, commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`;
`FsDurImg.v` §9a–c, lines 211–428, with the full-map and entry-free
validity foundations from `FsState.v`.

`LinkSupplyDefs.lean` defines the source authority map, full token supply,
full ownership map, combined outgoing entries, and ticket-list token fold.
All use the existing native `FsLink.FamilyRA` and Iris `bigOpM`/`bigOpL`.
No new camera, ghost slot, representation assumption, or image literal is
introduced. The input inode map may contain arbitrary durable nodes.

`LinkSupplyProofs.lean` closes these source dependencies:

- A generic per-key singleton-fold lookup preserves exact map domains.
  Authority, token-supply, and full-map lookups follow from it.
- `fullMap_valid` is unconditional: each inode has its own authority and
  matching full fragment. Authority-only and token-supply validity follow;
  a node's outgoing entries need not satisfy any condition for these laws.
- `fullMap_split` and `elem_split` expose the authority and fragment halves.
  `outgoing_one` isolates the only node with entries. `elem_valid_of_root`
  accepts an arbitrary spare camera element and derives actual native
  validity from its inclusion in the full token supply. No image validity
  premise is assumed in place of the inclusion.
- `tokens` preserves list multiplicity. A zero ticket count gives an absent
  key; a positive count gives the exact matching multiset fragment.
  `tokens_included_supply` proves native camera inclusion when every
  positive count has a present inode with sufficient multiplicity.
- Append, join, membership, singleton, and repeated-ticket laws preserve
  the source `tickCount` filter-and-length definition.
- Entry-free whole-family validity follows from the authority-only map.

The present-empty distinction is explicit: a zero-multiplicity inode has
a **present empty fragment**, while an empty ticket list has no keys.
`supply_zero_present` and `supply_zero_not_empty` prove this difference;
`tokens_empty_included_supply` proves that the latter is nevertheless
included in any supply. No quotient identifying these two maps is used.

Validation: `python3 tools/lake.py build Xv6.Fs.LinkSupplyProofs` passed
242 jobs; the new proof module took 1.3 seconds. The enforced namespace
audit checks all 45 declarations, including definitions and private helpers,
and accepts only `propext`, `Classical.choice`, and `Quot.sound` transitively.
A separate physical-module-origin audit passed all 46 declarations (also
including an imported definition's generated equation), traversing types
and bodies and rejecting unsafe or partial logical dependencies. No `native_decide`,
`bv_decide`, `sorry`, or custom axiom is used.

The subsequent LinkDirectory/LinkImage layers now discharge §9e's
directory-view-to-ticket inclusion and §9g–h's full image-family validity with
the root's spare token. `elem_valid_of_root` is the generic reduction for that proof;
it does not discharge its image inclusion hypothesis. Ownership packing,
allocation, and the complete durable snapshot tie remain later dependencies.
The frozen `FsLink` and `LinkFamily` modules were not changed.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
