# Virtio device port

The state/MMIO/reset/durable disk/sector layer and operational DMA definitions
compile. Driver queue obligations, Iris ownership, complete operational invariant
proofs and whole-system safety remain incomplete.

Owner: Codex Sail/device agent. Source: `iris/VirtioModel.v` at xv6iris
`arxiv-v1`, `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
The entire 2,447-line model was read before choosing the representation.

## Representation and source mapping

`Defs.lean` keeps all 12 source configuration fields and all nine device-state
fields. Addresses are `BitVec 64`; bytes are `BitVec 8`; MMIO offsets and durable
disk offsets are `Int`. The durable disk is a total `Int → BitVec 8`, independent
of the capacity field. `Cfg`/`State` also have source aliases
`virtio_cfg`/`virtio_state`; all fields and operations retain source names.

The finite volatile cache is `Std.ExtTreeMap Int (List Byte)` and the finite set
of in-flight descriptor heads is `Std.ExtTreeSet (BitVec 16)`. These are concrete
extensional containers, not arbitrary abstract map parameters or possibly
infinite functions. Iris already supplies `LawfulPartialMap` and
`LawfulFiniteMap` instances for `ExtTreeMap` in `Iris.Std.HeapInstances`.
`cache_ext`, `cache_lookup_finite` and `inflight_finite` expose extensional
lookup and finite enumeration laws. An eventual Rocq-to-Lean relation must pair
cache lookups and in-flight membership pointwise; enumeration order is not a
source observation (the future stalled check is an existential list scan).
No cross-assistant extraction/correspondence theorem is claimed.

| Source lines | Implemented definitions / proof families |
|---|---|
| 70–320 | All constants, `vq_size_ok`, `Cfg`, `State`, `set_vcfg`, `disk_view`, zero words, live/cache-mode/IRQ predicates |
| 334–648 | Exact MMIO register decode/write behavior; word splicing; reset; disk and capacity preservation for every successful MMIO store |
| 698–758 | `disk_read`, `disk_write`, `disk_wr`, `wr_apply`; readback, in-range/outside/nil and idempotence laws |
| 777–960 | Sector ceiling, count/coverage/bounds, chunking, sector write/miss/hit/outside; commutation and arbitrary-order complete reassembly |
| 974–993 | `cache_view`, miss and empty-cache collapse |
| 2290–2379 | Pure power-on state, capacity replacement, initial driver configuration, ISR predicate; initial live/cache-mode/reset ISR proofs |

Bitvector masking/splicing uses Lean's width-preserving primitives; five checked
half-extraction/reassembly laws certify the address behavior. Signed integer
bitwise queue-size arithmetic uses the existing `FromMathlib.Int.land` operation
from Iris. Source conditions with identical truth values can be Lean propositions
or Booleans; no guards or result alternatives have been removed.

The MMIO quirks are preserved: foreign queue writes and any notification are
accepted and ignored; illegal queue-zero sizes are rejected; unsupported offsets
return `none`; SHM region length/base reads return all ones; the aligned config
window reads zero after the two capacity words. Reset loses cache/inflight/latch
state but retains current disk bytes and capacity. `virtio0_state` is explicitly a
power-on helper and must not be used to implement reboot.

## Checked laws

`Proofs.lean` currently contains 56 named theorems, including:

- `virtio_write_durable`, `virtio_write_disk`, `virtio_write_cap`;
  `virtio_write_notify`, `virtio_write_ack`, `virtio_write_reset`.
- Reset disk/capacity/cache/inflight/taken/progress/IRQ/cache-mode preservation or
  clearing laws and idempotence; driver-init live/cache-mode laws.
- `set_lo_hi_id`, `set_lo_low`, `set_lo_high`, `set_hi_low`, `set_hi_high`.
- `disk_read_write`, `disk_write_in`, `disk_write_out`, `disk_write_nil`,
  `disk_write_idempotent`, `disk_write_congr_at`.
- `sector_count_cover`, `sector_of_bounds`, `sector_count_lt`, `sector_chunk_len`,
  `wr_sector_miss`, `wr_sector_outside`, `wr_sector_hit`, `wr_sector_write`.
- `wr_sector_comm` (also handles repeated sectors), `wr_sector_absorb`,
  `wr_fold_outside`, `wr_fold_hit`, `wr_fold_all`.
- `cache_view_miss`, `cache_view_empty` and finite-container laws above.

`wr_fold_all` requires only coverage of each valid sector index. It allows any
ordering, duplicates and additional out-of-range indices. Short final sectors
are retained. It is a disk-transformer theorem, not a claim that device drains
or kernel writes already satisfy the corresponding protocol.

Validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Devices.Virtio.Proofs
```

Passed 33 jobs; the corrected proof module compiled in 1.4 seconds. Proofs use
ordinary kernel checking, bit extensionality and `decide +kernel`, with no
`sorry`, new axioms, `native_decide`, or unsafe definitions. Independent review
caught that Lean's default `bv_decide` path introduced native-generated LRAT
axioms in three initial halfword proofs. All five `bv_decide` uses were replaced
with ordinary bit proofs before integration. The reviewer supplied the checked
reassembly proof; the owner implemented the four halfword projection proofs.
The corrected enforced whole-namespace audit passed all 136 theorem declarations
(56 public theorems plus generated helpers), permitting only `propext`,
`Classical.choice`, and `Quot.sound`. Independent review replayed every public
theorem and confirmed the same set. Review also resolved a stale source-comment
ambiguity: executable `virtio_pop` inserts the descriptor head read from the
available ring into `v_inflight`; `v_taken` holds such a head too. `v_seen` alone
is the ring position. The Lean state description follows executable definitions.

## Operational DMA slice

`Dma.lean` ports the executable definitions from source lines 682–694 and
1021–1886, using `MachCSL.Memory.ByteMap 64` and `Memory.Bytes` for the machine's
partial memory. It includes all of:

- `read_byte_list`, `write_byte_list`, `pa_off`, source little-endian
  `assemble_bytes`/`read_bytes`; `vmem`, `mem_view`, `view_bytes`, `view_word`.
- Descriptor and request records; `desc_at`, available-ring reads, `chain_from`,
  `virtio_chain_ok`, `req_from`, `vdist`, `vpos_pub`.
- `vreq_used_len`, `virtio_used_writes`, `vreq_wr`, sector counts/keys,
  `vreq_cache_of`, `vreq_cache`, `vreq_sectors`, `vreq_span`, `vreq_touch`.
- `virtio_complete`, `virtio_pop_ok`, `virtio_pop`, `virtio_pop_step`,
  `virtio_pending`, `virtio_serve_ok`, `virtio_complete_ok`, `virtio_req_step`,
  `virtio_capture_step`, `virtio_drain_step`, `virtio_stalled`.

Two representation adapters have explicit semantic laws: `cache_disjoint_spec`
identifies the finite Boolean test with absence of all selected sectors from the
cache, and `cache_overlay_lookup` gives exactly `fresh.lookup.or old.lookup`.
Cache construction uses a right fold so the first repeated key wins, matching
stdpp `list_to_map`; capture uses explicit left-biased merge. DMA writes use the
source's right folds and preserve modular-address overlap precedence. Partial
last sectors are retained, and arbitrary malformed raw cache lists are not ruled
out by the state carrier: the bound of 512 bytes per reachable drain is a future
capture/cache invariant obligation, as in the source.

The source's behavioral distinctions remain explicit:

- Total bus views are constrained only where the partial memory is defined.
- Pop advances `v_seen` and stores the descriptor head found in the ring.
  In-flight heads can be served in any order.
- Capture samples a write payload once, overwrites matching cache sectors,
  preserves disk/IRQ, and owns one head-specific latch.
- Completion gates distinguish OUT, FLUSH and other requests, including the
  source's writethrough read gate. Used length follows the descriptor writable
  flag even for unsupported request types. Completion updates status/ring/IRQ
  together and changes neither durable bytes nor cache.
- Any cached entry can drain without a RAM view or live-queue premise; reset
  discards remaining volatile state and preserves whatever already drained.
- Malformed in-flight chains set `virtio_stalled`. The parent machine relation
  must implement the source's wild-write rule, rather than making the device
  silently stuck or excluding bad requests from the state type.

`DmaProofs.lean` has 61 public theorems. These include the partial-read/total-view
bridge and uncached-span durable-read collapse; sector-set specifications; source pop/serve/completion/capture/drain
shape and field laws; completion gate inversions; malformed-chain/no-step and
stalled/pending implications; head-specific latch preservation;
`virtio_reset_after_drain`; and `empty_memory_has_distinct_views`.

Validation:

```sh
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Devices.Virtio.DmaProofs
```

Passed 38 jobs, proof module 861 ms. The enforced combined Virtio audit passes
256 theorem declarations (117 public plus generated/private helpers), with only
`propext`, `Classical.choice`, and `Quot.sound`. All-namespace audit source at the
research checkpoint is `/tmp/xv6-lean-research/VirtioAxiomAudit.lean`; integration
must retain the repository-wide physical-origin/transitive audit. Independent
Independent DMA source review passed; see `docs/reviews/virtio-dma-review.md`.
`Devices/MemoryBridge.lean` additionally proves equality of DMA and CPU byte
assemblers/readers for every input, removing their Nat/Int representation gap.

## Remaining obligations

Remaining: full byte/source representation correspondence; operational cache
bounds and queue geometry/lease/no-stall obligations; cache/drain
protocol and writethrough invariant; left-fold/drain sequence reassembly; kernel
driver initialization sequence; Iris device ownership, crash rules and closed
whole-system adequacy. This is a direct operational port with checked local laws,
not a closed xv6 theorem or a proved Rocq-to-Lean semantic equivalence.

The intermediate integer bit-twiddling helper lemmas `lor_split32` and
`mod_shiftr_id` are not separately ported: Lean proves the required address
reassembly result directly by bit reasoning. `virtio_state_eta` follows Lean
structure eta and is not a separately named lemma. Driver-facing pure queue
obligations from source §7 and full reachable-state preservation proofs are the
next device proof layer after machine integration.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
