# Direct native supervisor A/D update composition

This proposal covers the actual `update_and_write_pte 39 ... 0` program on
one directly owned kernel leaf slot. It composes the frozen native
SupervisorPteRead and SupervisorPteWrite wrappers with the coordinator's
KptLeaf validator. A shared KPT invariant accessor remains a separate
obligation; the direct slot theorem does not claim to supply it.

I read the complete generated `Vmem.update_and_write_pte:325–360`, its
read/write and leaf-check wrappers, the Svadu/Svade feature definitions,
`PtTreeAdue.v:1650–1818,1852–2045`, and `HartSKpt.v:730–910` at xv6iris
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The source distinction between
the cached PTE and the exclusive reread is retained throughout.

## Exact control flow

`update_PTE_Bits cached access = none` returns `.Ok (none, ())` immediately.
It performs no feature query, register read or memory event. Otherwise the
actual gate evaluates Svadu, menvcfg.ADUE, Svadu again and Svade. In the
pinned generated configuration both feature queries return pure true
(`PlatformConfig:2218–2219,2643–2644`). The complete gate therefore performs
one actual menvcfg read and tests ADUE. Its Boolean structure and all pure
feature calls are retained in the program factorization. ADUE false returns
`.Err (PTW_PTE_Needs_Update (), ())`; no reread or write occurs.

When ADUE is true, the program performs the actual exclusive eight-byte
PTE reread, then the actual level-zero leaf validation of that reread word.
The second `update_PTE_Bits` is applied to the reread, not the cached word:

- None returns `.Ok (some physical, ())` and retains the installed snapshot.
- Some new performs the actual conditional write. `.Ok true` returns
  `.Ok (some new, ())` and the successful event clears the reservation.
- The real write `.Ok false` reaches `internal_error` at
  `sys/vmem.sail:226`; it is not a retry loop. Write `.Err _` maps to
  `PTW_No_Access`; reread `.Err _` maps to the same error. Leaf errors are
  propagated exactly.

Pure factorization preserves all these residual branches. Concrete native
read/write and leaf proofs establish the successful responses under the
owned resources and configuration. No successful read, successful write,
state-preservation callback, or abstract leaf-correctness premise is accepted.
Native blocked rereads clear the local reservation and retry; blocked writes
retain the installed snapshot and state. Eventual completion is not claimed.

## Concrete leaf and register family

Use `Xv6.Kernel.KptLeaf.Permission.rx/rw`, `word ppn permission a d`,
`Supported access` and `Allows permission access`. The physical word is
`word ppn permission a d`; the cached word is independently
`word ppn permission cachedA cachedD`. All four A/D bits are arbitrary.
The reference byte family is `PteCanonical.slotSet
(word ppn permission false false)`. This is a concrete source leaf family,
not an assumed validator or consistency oracle. PPN is an arbitrary 44-bit
word, with no chosen physical mapping.

The native footprint contains the existing four fractional PMA/PMP/HTIF
cells plus one fractional menvcfg cell for the ADUE gate. Config combines
actual SupervisorPteRead.Config and SupervisorPteWrite.Config, requiring
both supports_pte_read and supports_pte_write, the existing TOR grant,
aligned eight-byte RAM range and disabled HTIF. It leaves menvcfg otherwise
arbitrary. ADUE=true is a later source-regime specialization, not a hidden
assumption excluding the gate's error return.

KptLeaf's complete validator has `RegisterPlan.Returns [] ...`: every eager
MISA/menvcfg read is justified for every possible result. Those remain real
register events and require no duplicate cell. Its exact permitted access
family is fetch, Data load/store and Data AMOSWAP with arbitrary aq/rl;
fetch requires RX and stores/swaps require RW. MXR and SUM remain arbitrary.
The physical PTE read/write wrappers still use Load/Store PageTableEntry,
independent of the translated access kind.

## Native resource and continuation contract

Owned files are new `MachCSL/Logic/SupervisorPteAD` Defs/Spec/FactorDefs/
Plan/Pure/Slots/Proofs/Link, and STATUS. No existing
module or camera slot changes.

The public input is generationCertificate, the five-cell register bundle,
any current reservation fragment, and the existing full
`TsoPinnedReadWP.slot` for the physical word and reference family. A boot
publication credential is unnecessary for an exclusive reread. The slot
still contains all exact source per-byte floors, timestamps, allowed sets,
and the three publication-anchor alternatives.

Use a finite Branch datatype: cached, disabled, reread, or written new.
`BranchFacts` records the actual cached/reread update equations and actual
ADUE bit selecting that branch. The returned result, new physical word and
reservation are defined by the branch:

| Branch | Result | Physical word | Reservation | Additional receipt |
| --- | --- | --- | --- | --- |
| cached | Ok (none, ()) | original | incoming rr | none |
| disabled | Err (NeedsUpdate, ()) | original | incoming rr | none |
| reread | Ok (some original, ()) | original | snapshot of original | reread viewLB |
| written new | Ok (some new, ()) | new | none | positive authored time, exact logElem(time−1), viewLB time |

Every final branch returns the same five cells and the complete slot in
its unchanged reference family. A single genuine continuation contract
quantifies Branch and its pure BranchFacts, then receives that branch's
resources and proves the WP of the actual final continuation. It never
returns a callee/body WP or an assumed successor interpretation.

The continuation guard contributed by the memory primitives is zero for
cached/disabled, one for reread, and two for written. Implement this as an
explicit branch-indexed guard, not an unconditional guard that would let
a pure cached return consume a memory step. Register steps are still folded
by their own native rules. Expected actual path counts, to verify against
the composed plans, are zero events for cached; one register read for
disabled; thirteen register reads plus one memory read for reread; and
eighteen register reads plus one memory read and one write for written.
These counts are not premises of the theorem.

## Slot extraction and write reconstruction

The original slot hides each byte's floor and timestamp. Before the actual
write, prove the finite eight-byte equivalence exposing a floor function:

```text
slot a 8 (own 1) (nthByte physical) B sets
  ≡ ∃ floors,
      pinWindow a physical (own 1) floors sets ∗
      [∗ j<8] (pure (floors j ≤ B) ∗ slotAnchor (a+j) (floors j))
```

The metadata part is persistent. This is a proved regrouping of existing
resources, not an added publication assumption. The current native pinned
write consumes the full pinWindow and returns storedWindow at the actual
new authored time. Reattach every original floor/anchor to reconstruct the
same slot predicate with the new word. PteCanonical plus KptLeaf's checked
word laws prove new-byte membership and unchanged canonical family. No
extra no-wrap hypothesis, updated publication bound or second physical
fraction is introduced.

At the source shared-table seam, the invariant must be closed between the
reread, leaf checks and conditional write. This direct theorem instead owns
its slot throughout. It can represent different cached and already-updated
physical A/D bits, but is not the predicate-indexed shared reread accessor
of PtTreeAdue's complete `swp_update_and_write_pte_ex`. The later shared
version must construct real per-event accessors and preserve canonical-tree
agreement. That work cannot be replaced by assuming this direct ownership
is available across an open invariant.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
