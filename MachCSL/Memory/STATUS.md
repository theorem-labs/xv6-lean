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
without changing the partial lookup space. The language integration still owes
an explicit correspondence with its chosen concrete finite-map representation.

The source `read_down` checks the visible timestamp zero and then falls through
to `None` if no byte exists. Lean expresses that base case directly; since zero
is always visible, it has the same result. Source `own_pub` uses indexed mapping
followed by a right-fold of maximum; Lean uses `zipIdx` and the same fold.
`addressAdd` wraps at the address width; `nthByte` extracts a little-endian byte.
Their correspondence to Sail `pa_add`/`nth_byte` is not yet proven.

`ReadsBytes` is a relation over one shared view; it must not be replaced by
independent per-byte view choices. No load/store transition relation is invented
here: nondeterministic view advancement, exclusive read/write atomicity,
reservation protection, and the definition of draining fence kinds belong to
the source's `RiscvLang.mnode_step` and remain to be ported.

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

Not yet ported: `write_bytes_union` and `flat_store`; the reverse existence
`flat_latest`; the source's byte pins, word windows, release-history predicates,
word-set pins, and `ts_ok` ghost interpretation; finite-map/Sail correspondence;
`RiscvLang` stepping; Iris resource interpretation and adequacy.

Next bounded task: implement the shared byte-write operation and prove the
snapshot-overlay/flat-store correspondence at the 64-bit carrier, then connect
this core to the exact Sail event memory interface before higher ghost-state
proofs depend on it. Keep later changes to the upstream relaxed-R→R model out
of this paper-baseline port.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
