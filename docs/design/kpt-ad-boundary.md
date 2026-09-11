# Native shared-KPT A/D program boundary

KptAD composes the actual `update_and_write_pte 39` at supervisor privilege,
level zero, with the shared kernel tree clients. Defs/Spec compiled at 435
jobs and received coordinator signature approval before implementation.
The implementation now constructs all three native rules in seven modules;
`KptADLink` builds at 794 jobs and the full 102-declaration audit passes with
zero exclusions. The ownership prefix is Xv6/Kernel/KptAD*. No existing
frozen module changes.

The initial inputs are five fractional physical register cells (PMA regions,
PMP config/address arrays, HTIF base and MENVCFG), their explicit native read/
write Config, generation certificate, shared invariant and canonical snapshot,
a pure Maps path in that snapshot, and the incoming reservation fragment.
The address equals the exact leaf slot PtTree.addr0 of the raw level-one
pointer and VPN. Kernel permission is rx/rw with an actual Supported access
(fetch, load, store or swap) and Allows proof. Cached A/D bits are independent
of the snapshot A/D bits. mxr and doSum are arbitrary. No owned physical slot,
current leaf value, access callback, restoration wand, chosen response or
software-success premise is an input.

Source: complete generated Vmem.update_and_write_pte:325–360 and existing
SupervisorPteAD factorization; HartSKpt.v:748–902 shared leaf write and
1020–1325 shared translation composition; PtTreeAdue.v exclusive/conditional
node wrappers and predicate-indexed A/D composition. Source pin
fa7f0a01c4b40489fac8ad303f079c2dfc7a1476, model pin
23dcf8fd923eb8a1958795393d2975632aa940b2. This is source correspondence,
not a formal cross-prover equivalence.

The actual branch structure is retained:

| Branch | Actual result | Reservation | Memory guards |
| --- | --- | --- | --- |
| Cached update=None | Ok(None, unit) | incoming rr | 0 |
| Cached needs update, ADUE disabled | Err(PTW_PTE_Needs_Update, unit) | incoming rr | 0 |
| Enabled, exclusive observed word needs no update | Ok(Some observed, unit) | snapshot of observed eight bytes | 1 |
| Enabled, observed update=Some new, conditional write completes | Ok(Some new, unit) | none | 2 |

No initial physical value can index the last two branches: the exclusive
shared event selects it from the actual current state. Branch.reread carries
observed; Branch.written carries observed and new. BranchFacts supplies the
actual cached/observed update equations, ADUE and canonical equalities as
proved outputs. Those pure facts sit inside each branch's guarded genuine
continuation, allowing selection of the unknown observed value after the
real read. The two result families quantify all observed words and new words;
there is no chosen-memory witness in the interface.

Both feature probes are retained by the existing actual factorization. In
this pinned model Svadu/Svade support is fixed and the noncached gate reduces
to one real MENVCFG read. ADUE is not fixed. The exclusive PTE prefix has five
actual register reads; the real kernel-leaf validation retains seven universal
register reads; the conditional PTE prefix has five. Thus cached needs none,
disabled needs one, reread-only needs thirteen, and written needs eighteen
register reads, in addition to zero/one/two real memory events. The five owned
cells are restored throughout; universally read validation fields are not
turned into extra owned cells or reference-state assumptions.

Shared exclusive read opens/closes the invariant only at its event and
returns the actual canonical word, snapshot reservation and selected-view
receipt. It needs no boot/view publication credential because it reads current
physical memory exclusively. The caller's cached word may have come from the
ordinary shared walk or a coherent stale TLB entry; those separate callers
supply the Maps/canonical relationship. KptAD inserts no ordinary memory read.
The written branch pays the actual conditional event through KptWriteEvent,
returning its positive authored timestamp, exact history element, final view
receipt and cleared reservation. All branch outputs retain the same shared
invariant and canonical snapshot. The final write receipt suffices for this
contract; no new claim about ordering it against an unrelated receipt is made.

The exact generated factors retain read errors, leaf-check errors, write
errors and the `Ok false` internal_error. They are not converted to retry or
silently removed from a copied program. Native RAM event rules and concrete
hardware/permission plans discharge those paths on the supported inputs.
Blocked exclusive read and blocked conditional write remain covered by their
native loop rules; there is no eventual-success or pairwise-reservation
premise. Reread-nochange keeps its new snapshot; success clears it.

Spec exposes the two actual read_pte_exclusive/write_pte_conditional wrapper
rules and the complete A/D program rule. Prefix induction reuses the frozen
SupervisorPteRead/Write Boundary proofs, substituting constructed shared event
rules only at their genuine event. The MENVCFG cell is framed once around
these four-cell wrappers. No invariant remains open over a register or memory
event. Full translate_TLB_hit/miss, TLB coherence updates, virtual-memory
translation, initial KPT publication and kernel boot reachability remain
separate. This slice introduces no camera or registry slot.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
