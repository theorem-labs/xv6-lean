# Native inode escrow tokens

The four `IcacheEscrowTokens{Defs,Spec,Proofs,Link}` modules are frozen after
owner validation. They implement the complete token vocabulary in pinned
`EscrowDefs.v:1–136`, with the exact relevant camera fields and corpse carrier
from `Xv6Cameras.v:820–885`. The approved design is
`docs/design/icache-escrow-tokens-boundary.md`.

| Source | Lean implementation |
| --- | --- |
| `EscrowDefs.v:22–28` | Native `committedA`, mono-nat lower bound 1 at the explicit escrow name, Persistent and Timeless |
| `30–39` | Nonunital `Excl Unit` ticket, `redeem_ticketA`, native exclusivity |
| `45–68` | Exact `Corpse.pre transaction share`/`deposited` carrier, full native `crp_elem`, per-key exclusivity |
| `70–84` | Native registry `reg_half` and `reg_full` at the same supplied map name, signed key and exact escrow-name pair |
| `87–124` | Pair agreement, full/half exclusion and exact half join/split |
| `128–135` | `region_pending = ∃ ge gr, reg_half z ge gr ∗ committedA ge`, Timeless |
| `Xv6Cameras.v:851–852,885` | Explicit ticket, registry and corpse capacities; exact source raw cameras |

The implementation retains the complete raw `Excl Unit` carrier, including
its invalid constructor. It does not replace the ticket by an authoritative
Boolean or the pending payload by a pure tag. The corpse pre-deposit value
retains its exact transaction Nat and positive Qp share; the generic
fractional agreement theorem projects equality of both fields. The deposited
constructor has no hidden payload.

The resource layer also exports native full map authority and general
fractional element lookup for the registry and corpse maps, fresh-key
insertion, existing-key update with the complete fragment, full-fragment
deletion, and fresh empty-map allocation preserving an arbitrary frame.
Named framed update laws preserve both the exact replacement row and the
caller's frame. A fresh ticket allocator similarly allocates only at a fresh
existential name in the supplied world. There is no arbitrary-name mint,
InvGS world allocation, initial-snapshot constructor or replacement of
existing authority. Map updates use the lawful finite map's exact insert
and delete operations, including the distinction between an empty owned map
and no authority resource.

`region_pending_intro/open` retain the exact escrow-name pair and committed
fragment. `reg_full_pending_False` derives the slot-arm refutation directly
from its real full/half fraction overflow. `committedA` is only the source
persistent lower bound; this module does not infer an escrow invariant,
physical deposit, redemption or a parked transaction resource from it.

The concrete registry extends frozen `LogEpoch.registry` with slot 35 for
`GhostMap Int (GName × GName)`, slot 36 for `Excl Unit`, and slot 37 for
`GhostMap Int Corpse`. Checked preservation covers every old slot 0–34 and
all unused positions 38 onward. The mono-nat field reuses slot 3 at explicit
names. Existing machine/era, memory, disk, invariant/InvGS, UART, filesystem,
lock, record, count/mirror/pin, reference, type, transaction and log-epoch
capacities are exported in the same world. Slot equalities and the shared
mono-nat equality are kernel-checked.

Validation: `python3 tools/lake.py build MachCSL.Logic.IcacheEscrowTokensLink`
passes all 476 jobs. The four files contain 62 named theorems and 11 native
resource instances. Fresh `/tmp/xv6-lean-research/IcacheEscrowTokensOwnerAudit.lean`
checks all 241 logical declarations from the four physical origins, including
private/generated helpers, opaque bodies, types and datatype constructors.
Only `propext`, `Classical.choice`, and `Quot.sound` occur; zero roots are
excluded and there are no unsafe/partial or `FsDurSnapshot.Initial`
dependencies.

The whole escrow empty/filled/redeemed invariant, its body, free-pool state,
corpse ledger's parked resources, deposit/redeem program rules, complete
icacheG and full inode-slot/region boot assembly remain separate source
obligations. This boundary provides their actual native tokens and map
operations without assuming those later relationships.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
