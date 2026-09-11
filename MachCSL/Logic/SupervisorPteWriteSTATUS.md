# Checked supervisor conditional PTE write

Frozen five modules: SupervisorPteWrite Defs/Spec/Plan/Proofs/Link.
`actual` and `nativeSpec` construct the public native WP for the real
generated `write_pte_conditional` at width eight.

The program is exactly `mem_write_value_priv` followed by its actual
`checked_mem_write`, with `Store PageTableEntry`, `PBMT_PMA`, explicit
Supervisor and false/false/true flags. It does not call write-EA or the
effective-privilege wrapper. The four-cell fractional footprint owns PMA
regions, the PMP config/address arrays and HTIF base. The prefix retains
five register reads: PMA, PMP config, PMP config again inside address
lookup, PMP address and HTIF. It neither owns a whole register file nor
invents status/privilege reads.

Config retains source TOR permission/range, actual PMA match,
`supports_pte_write`, disabled HTIF and eight-byte alignment. The grant is
not the ordinary `writable` flag. The actual conditional PTE PMA arm has no
Data-store assertion, and the proof preserves the true conditional flag.
MAG/alignment handling proves the actual one-iteration split loop.
The local `pmp_store_pte_eq` is a kernel-checked equality of the entire
generated PMP trees for arbitrary privilege, address and width; it allows
reuse of the existing TOR Data-store grant because only identical RWX and
fault classifiers depend on the payload there. PMA and the final write
keep their exact PTE/conditional semantics. No frozen Supported enum or
other module was edited.

`OneWrite` reuses the existing generic SupervisorWrite boundary. Its
actual residual maps every raw successful optional payload to true and
raw error to false; no arm is erased. `checked_boundary` and
`program_boundary` construct this boundary from concrete register plans,
including the real write-kind selection, MMIO test, singleton data
extraction and Boolean accumulation. `program_eq` proves the actual pure
callback wrapper equality, retaining both success and failure results.

`fold_boundary` uses native fractional RegisterPlan rules for the prefix
and TsoPinnedWriteWP for the real event. The public theorem supplies its
entire boundary internally and takes no access payer or successor oracle.
It preserves the four register cells and supplies the final continuation
with all new pins, the positive authored timestamp, exact history receipt,
cleared reservation and matching top-view receipt. Blocked writes retain
the old state, snapshot reservation and payer. `event_step_inv` exposes
both blocked and committed arms; there is no pairwise-reservation
separation or eventual-success hypothesis.

Scope: actual generated `Vmem.write_pte_conditional:226–229`,
`Mem.pmaCheck:262–341`, `Mem.checked_mem_write:534–582`, value wrappers
586–598 and `PhysMemInterface.write_ram:292–326`; source write-node
obligations `HartSKpt.v:759–906` and `PtTreeAdue.v:1213–1237` at
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. The source shared KPT invariant,
canonical-tree accessor, preceding exclusive reread/update logic and full
Sv39 translation remain separate. This direct physical wrapper alone is
not the complete shared page-table proof or disabled-SIE mycpu proof.

Validation: Link build passed **500 jobs** (Plan 1.4 s, Proofs 1.0 s,
Link 839 ms). Fresh physical-origin audit checked **177 declarations**
across all five modules, including private helpers, all transitive types,
opaque proof bodies and constructors. Only `propext`, `Classical.choice`
and `Quot.sound` occur; **zero exclusions**, no unsafe/partial logical
dependency and no custom/native decision axiom. Earlier elaboration
failures were fixed before this successful final build. Evidence:
`/tmp/xv6-lean-research/SupervisorPteWriteAudit.lean`,
`supervisor-pte-write-build.log`, `supervisor-pte-write-audit.log`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
