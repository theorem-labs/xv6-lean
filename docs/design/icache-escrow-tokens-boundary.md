# Native inode escrow token boundary

Approved boundary: `IcacheEscrowTokens{Defs,Spec,Proofs,Link}` and STATUS,
implementing all token definitions in pinned `EscrowDefs.v:1–136` using the
exact component cameras from `Xv6Cameras.v:820–885`. The escrow invariant and
its body are separate source components above this file.

Three newly assigned slots extend the existing LogEpoch registry: slot 35
is a native `GhostMap Int (GName × GName)`; slot 36 is the nonunital raw
`Excl Unit` redemption-ticket camera; slot 37 is a native
`GhostMap Int Corpse`, where `Corpse.pre` retains the exact transaction Nat
and positive Qp share and `Corpse.deposited` carries no data. All prior slots
0–34 and unused positions 38 onward are preserved. The complete raw Excl
carrier, including its invalid constructor, remains represented. Existing
mono-nat slot 3 is reused at separate explicit ghost names.

The source predicates are direct ownership definitions. `committedA ge` is
the mono-nat lower bound 1 at ge, not a pure Boolean or a complete escrow
invariant. `redeem_ticketA gr` owns `Excl ()` at gr. `reg_half` and `reg_full`
share a supplied registry name, signed inode key and exact escrow-name pair,
using owned one-half and one respectively. `region_pending z` is exactly
an existential pair ge/gr, half registry fragment, and committedA ge.
`crp_elem` owns the full fragment at a supplied corpse-registry name and
signed inode key. No transaction share is existentially erased from a
corpse value.

The public native laws include ticket and corpse exclusion, pair agreement,
full/half exclusion, exact half split/join and pending introduction/opening.
Generic registry and corpse APIs expose full authority, fractional fragment
lookup, fresh-key insertion, existing-key update with the complete fragment,
delete with the complete fragment, and empty allocation with an arbitrary
frame. These operations preserve exact map insert/delete behavior. A
single named empty map is not treated as an absent resource. Allocating a
fresh redemption ticket or map name stays inside the same supplied world;
no InvGS world is allocated. There is no arbitrary-name ticket mint.

All definitions remain separate from proofs. Generic capacities come first;
the concrete Link extends frozen LogEpoch34 and exports explicit existing
capacities and InvGS links. This establishes the native token boundary
needed by the inode slot's registry and pending arms. It does not implement
the escrow's empty/filled/redeemed invariant, free-pool body, deposit/redeem
program rules, corpse ledger's parked transaction resources, or complete
icacheG. Those bodies must later relate these actual tokens to the source
physical and logical resources rather than replace them with pure facts.

Validation will compile the exact source API and audit all physical module
origins with opaque bodies, types and datatype constructor dependencies;
only the standard three axioms are allowed. Existing frozen modules remain
unchanged.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
