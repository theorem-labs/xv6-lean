# Production TSO memory: first proof slice

This directory partially ports `iris/TsoMemPa.v` from mit-pdos/xv6iris tag
`arxiv-v1`, commit `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
It is not a whole-system model or an xv6 verification theorem.

`Defs.lean` defines the source's production byte-map messages, timestamped log,
below-view-or-own visibility, descending latest-visible read, common-view
multi-byte read predicate, last publication, draining fence, flat published map,
sole-author predicate, and latest-write predicate. `Proofs.lean` proves 32 public
lemmas. `Litmus.lean` proves seven concrete examples by kernel reduction.

## Representation and boundary

Addresses are `BitVec width`; the paper's Sail `Arch.pa` is a 64-bit carrier
(`model-xv6iris/rv64d_types.v:14781`), despite its separate 56-bit physical-address
validity bound. `PhysicalAddress` therefore aliases `BitVec 64`.

A `ByteMap width` is the extensional partial function
`BitVec width → Option (BitVec 8)`. The domain is finite, so every such function
represents a finite byte map. This removes stdpp map implementation details
without changing the partial lookup space. `FiniteMap.lean` now proves lookup, round-trip, support, overlay and write
correspondence with Lean ExtTreeMap. Its exhaustive finite-domain encoder is a
logical witness and must not be evaluated at 64 bits. Correspondence with the
source stdpp representation remains open.

The source `read_down` checks the visible timestamp zero and then falls through
to `None` if no byte exists. Lean expresses that base case directly; since zero
is always visible, it has the same result. Source `own_pub` uses indexed mapping
followed by a right-fold of maximum; Lean uses `zipIdx` and the same fold.
`addressAdd` wraps at the address width; `nthByte` extracts a little-endian byte.
Their correspondence to Sail `pa_add`/`nth_byte` is not yet proven.

`ReadsBytes` is a relation over one shared view; it must not be replaced by
independent per-byte view choices. The source's nondeterministic view advancement, exclusive read/write atomicity,
reservation protection and draining fences are now implemented in
`Machine/Node.lean`; their complete memory/reservation invariants are proved in
`Machine/NodeInvariants.lean` and lifted to arbitrary finite schedules.

## Source mapping

| Rocq source | Lean declaration |
|---|---|
| `bytemap`, `pwmsg` | `ByteMap`, `Message` |
| `msg_byte`, `log_byte`, `visibleb` | `msgByte`, `logByte`, `visible` |
| `read_down`, `tso_read`, `tso_read_bytes` | `readDown`, `read`, `ReadsBytes` |
| `own_pub`, `fence_post`, `flat` | `ownPub`, `fencePost`, `flat` |
| `all_own`, `latest` | `AllOwn`, `Latest` |
| `visibleb_below/own/le/app` | `visible_below/own/mono/append` |
| `read_down_0/total/app_below/vis_irrel` | `readDown_zero/total/append_below/visibility_irrel` |
| `tso_read_total/own_top/top_flat/all_own/of_latest` | `read_total/own_top/top_flat/allOwn/of_latest` |
| `log_byte_some_le/app_le/top/beyond` | `logByte_some_le/append_below/top/beyond` |
| `flat_snoc`, `own_pub_le` | `flat_append`, `ownPub_le` |
| `latest_app_new/app_frame/flat` | `latest_append_new/append_frame`, `latest_flat` |
| `all_own_nil/app/visible` | `allOwn_nil/append/visible` |

Additional helper facts: `visible_zero`, `logByte_zero`, `flat_nil`,
`fencePost_mono`, `fencePost_le_length`, `readDown_of_latest`,
`read_above_top_flat`. Private helpers prove maximum-fold bounds and reverse
list induction; none assumes a model property.

Litmus declarations in `MachCSL.Memory.Litmus`: `store_buffering_allowed`,
`own_stores_forward`, `drain_views`, `drained_store_buffering_not_both_zero`,
`full_view_published`, `foreign_write_supersedes_forwarding`,
`nondraining_fence`. These use the 64-bit carrier and two byte locations. They
check specified legal views and mandatory forwarding; they are not proofs of
full machine executions or all possible fence schedules.

## Validation and remaining work

The three files compiled with Lean 4.32.2. `#print axioms` was run on all 39
public theorems: only Lean standard `propext` and `Quot.sound` appeared; three
results needed no axioms. No `Classical.choice`, `sorryAx`, native decision
axiom, or custom axiom appeared. Commands used the explicit compiler selector
`lean +leanprover/lean4:v4.32.2`, with `LEAN_PATH=.` and dependency `.olean`
outputs to allow standalone checks before root Lake integration.

`Bytes.lean` now proves `writeBytes_overlay` (source `write_bytes_union`),
`flat_writeBytes` (source `flat_store`), modular write footprints, snapshot
coverage and preservation of disjoint submaps. `ReservationProofs.lean` supplies
the snapshot/read correspondence required by successful exclusive accesses.
The source right-fold write order is preserved even when addresses wrap.

`flat_latest` now proves that every published byte has a latest timestamp.
Remaining pure and logical layers include byte pins, word windows, release-history predicates, word-set pins and the complete
`ts_ok` interpretation; source Sail/map correspondence; and Iris resource
interpretation and adequacy. The machine transition transcription and its
structural invariants are now implemented, independently of those logical layers.

## Byte assembly and executable reads addendum

`ReadBytes.lean` now ports all byte-assembly and read lemmas in
`iris/RiscvModelBytes.v:45–207` at the same pinned paper commit. The adjacent
`pa_add`, `nth_byte`, and `write_bytes` definitions already have counterparts in
`Defs.lean` and `Bytes.lean`. This updates the earlier milestone description;
`Machine/Node.lean` also now supplies the source-shaped memory transitions.

| Rocq source | Lean declaration in `MachCSL.Memory` |
|---|---|
| `assemble_bytes` | `assembleBytes` |
| `nth_byte_unsigned` | `nthByte_unsigned` |
| `bv_eq_of_bytes` | `bv_eq_of_bytes` |
| `assemble_bytes_bound` | `assembleBytes_bound` |
| `assemble_bytes_byte` | `assembleBytes_byte` |
| `nth_byte_assemble_len` | `nthByte_assemble_len` |
| `read_bytes`, `read_bytes_spec` | `readBytes`, `readBytes_spec` |

The assembler returns `Nat`, representing the source's nonnegative integer
result; its lower bound is automatic. `readBytes memory address n` gathers the
`n` bytes in increasing offset order and returns `Option (BitVec (8 * n))`.
Every address uses modular `addressAdd`; no no-wrap hypothesis is needed, and
any missing byte makes the read fail. The successful-read theorem identifies
every returned byte with the corresponding memory lookup. The additional
`readBytes_of_bytes` and `readBytes_eq_some_iff` prove the converse, including
zero-width reads. These are general kernel-checked theorems, not tests of a
particular memory image.

Validation: `python3 tools/lake.py build MachCSL.Memory.ReadBytes` passes with
Lean 4.32.2. All eight public theorems were audited with `#print axioms`:
`nthByte_unsigned` needs none; the source-shaped lemmas use only `propext` and
`Quot.sound`; the converse and combined equivalence additionally use standard
`Classical.choice`. There are no custom or native decision axioms. Separate
ordinary `decide` checks confirmed wrapped two-bit-address reads, missing-byte
failure, and the empty read. The Nat/Int assembler and complete CPU/DMA reader correspondence are now proved
in `Devices/MemoryBridge.lean`; correspondence with imported Rocq definitions
remains separate. This module alone establishes neither a fetched instruction
execution nor kernel safety.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
