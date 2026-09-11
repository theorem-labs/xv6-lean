# Independent pinned-read event review

Result: PASS for TsoPinnedReadWP Defs/Spec/Pure/Proofs/Link, its design and
final STATUS. No production correction is requested. Review performed by
the OpenAI Codex sail_audit agent independently of the coordinator's work.

Read all five modules, the existing exact publication/pin definitions and
native slot_read proof, MemoryReadWP's plain premise and actual-step
inversion, and MemoryExclusiveWP's physical read, reservation and retry
proofs. Source correspondence is the context-free CtxValues publication/pin
boundary and actual common-view NodeStep read semantics, with the already
checked PteCanonical source family reused for the PTE specialization.

The ordinary rule is independent of any fixed physical word. It obtains
SlotReads from actual timestamp/history/view resources under the complete
live era interpretation, then assembles one word from the bytes of one
common read view. Classical choice selects witnesses of proved per-byte
reads; it supplies no extra byte or execution oracle. The assembly theorem
covers arbitrary dependent n, including zero, and proves every component
byte of the resulting word. The native lower rule considers every actual
successor and uses read uniqueness at its selected view, so the chosen
progress witness cannot restrict the machine's nondeterministic view.

The power-access proof restores all original era conjuncts after borrowing
the pure all-view property. Publication credential and the complete slot
return unchanged. The caller's reservation rr is framed through the actual
plain read; one memory step discharges exactly one later guard. The native
view update and its lower-bound receipt are retained. The physical value
function remains independent of the PTE reference and the eventual word.
The PTE rule derives canonical equality, and exact equality only under the
source nonleaf condition, from the allowed-byte family.

For the exclusive path, slot_physical is an affine projection if used by
itself. In the public rule it is used only inside heap_slot_read's pure
conclusion, which is borrowed with `ihave %reads`; the original slot is
therefore retained in the callback. The native heap authority proves the
readBytes equality, with the coherent era heap/TSO ledger and names made
explicit. No pin timestamp, floor, set or anchor is lost, and no physical
byte token is duplicated in the returned resources.

The reused exclusive rule advances to the real log top and installs the
exact snapshot reservation on success. Its blocked arm clears the local
reservation, retains the read obligation and retries by guarded induction;
it does not assume exclusive acquisition always succeeds. The callback
restores the supplied register/heap/device bundle and TSO resources at the
proper mask, then receives the actual updated reservation fragment. No
publication credential is needed for this physical-read derivation.

All request metadata remain carried by the original dependent read event.
RAM and ordinary/exclusive classifications are explicit. The design and
STATUS correctly distinguish this direct owned-slot boundary from a shared
KPT invariant accessor or a complete hardware page-table walk. No new
camera, Initial allocation, generated-code edit or fixed-word premise is
hidden in the public Spec.

Validation: the final STATUS reports 572 build jobs. This review freshly
ran `tools/lake.py env lean
/tmp/xv6-lean-research/TsoPinnedReadWPRootAudit.lean`, producing
`/tmp/xv6-lean-research/tso-pinned-read-wp-peer-audit.log`. All 26 logical
declarations from the five physical origins passed, including all private
and generated roots, transitive opaque bodies, types and datatype
constructors. Only propext/Classical.choice/Quot.sound occur, with zero
exclusions and no unsafe/partial or Initial allocator dependency.

| File | SHA256 |
| --- | --- |
| Defs | `394ec9c730afd746be7080fb0d28b2e11815899019179db3c77b1fc712e2844d` |
| Spec | `cd09d45d4e77e33bd2ff5530520272b58d0664ce3ac2845af159858e624734c2` |
| Pure | `2834df015a5fcc91b25ffa5dc49e2347a3399cc5457433c647c42f86c2884fc9` |
| Proofs | `a83b66173bcbce832cfedd257e64af5c04ae625660a1f4631425ad92a5091283` |
| Link | `b5a0ac592836510c162354c1b6d910df763a1ead19b6534065ed4a6af165f064` |

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
