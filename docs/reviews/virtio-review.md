# Independent review of the initial Virtio pure slice

Reviewer: Codex artifact-audit subagent. Author: Codex sail-audit subagent.
Baseline: xv6iris arxiv-v1, fa7f0a01c4b40489fac8ad303f079c2dfc7a1476.
Reviewed files: MachCSL/Devices/Virtio/Defs.lean and Proofs.lean.
Review passes for the implemented pure slice after replacing native-generated
proof axioms. No semantic mismatch was found in its executable definitions.
Final compilation and transitive axiom evidence are recorded below.

## Source comparison

The reviewed source covers VirtioModel.v constants/configuration/state/MMIO
through line 598, disk and sector operations at 696–993, and power-on/init/status
helpers at 2290–2379. DMA capture/completion/drain is not implemented in this
slice and was not mistaken for an implemented device thread.

- All 57 shared literal numeric constants match automatically, including device
  IDs, queue bounds, every MMIO offset and sector/window sizes.
- State field order, bit widths, selector storage, pop and used-ring indices, in-flight descriptor heads,
  optional captured head, volatile cache and durable-capacity fields match.
- Device-feature reads honor selector 0/1; higher selectors read zero. Unknown
  driver-feature selectors accept and ignore writes. Nonzero selected queues
  report absent and accept ignored writes. Queue 0 rejects illegal sizes.
- Queue notifications accept every value as a hint/no-op. Shared-memory
  length/base reads return all ones; queue-reset reads 0 but its write remains
  unsupported. Aligned unmodelled configuration words are zero only in the
  source's 0x100–0x200 window. Other unsupported MMIO operations return none.
- Every address half-word write updates the correct desc/avail/used field and
  preserves the other half. ISR acknowledgements clear exactly mask-selected
  bits, including arbitrary pre-existing ISR bits.
- Reset drops configuration, ISR, indices, inflight, cache and taken latch while
  preserving the current durable disk and capacity. It never substitutes the
  initial blank disk or fs.img. The separate initial state has the source's
 128-sector conformance-board capacity and blank total disk; it is not reboot.
- Disk read/write retain Int offsets. Byte lookups beyond a written list read
  through, and negative disk offsets are not silently rejected or naturalized.
  Sector count rounds up, including a partial last sector; wr_sector slices
  exactly 512 bytes at 512*i, and wr_fold keeps the source's right-fold order.
- Cache keys are absolute signed sector numbers. Positive-denominator integer
  division/modulo agree with the source for negative addresses too. Missing
  cache keys and missing bytes in a short cached sector fall back to the durable
  disk at that address.

Cache and DiskMap use Std.ExtTreeMap with Int keys, and Inflight uses
Std.ExtTreeSet with 16-bit keys. These are finite extensional containers,
consistent with the source gmap/gset carriers. Their internal ordering must not
be used to restrict future nondeterministic completion/drain choices. No such
restriction exists in the current pure slice. The future DMA model still needs
an arbitrary total memory view agreeing with known map entries; supplying a
fixed missing-byte default would narrow the source transition relation.

The structural proof statements inspected agree with their source claims.
Additional reset disk/capacity/idempotence and half-word projections strengthen
convenient local interfaces without weakening hypotheses. Full original-byte or
cross-prover equivalence is not asserted by these source comparisons.

## Validation checkpoint

The author reported a successful 33-job build. An independent frozen proof
snapshot, SHA256 `0ad1512d6b60c8392d48439a356a72139b4c03ea99d5e8b44a868d336aba60e8`,
was compiled with the repository Lake wrapper and all 56 public theorem axiom
cones inspected. The snapshot also includes correct finite-container witnesses,
sector commutation and full-write reassembly allowing arbitrary order,
duplicates and extra out-of-range sector indices.

**Resolved blocking finding:** `set_lo_hi_id`, `set_lo_high`, and `set_hi_high` depend on
new native-generated `..._native.bv_decide.ax_1_5` axioms. Lean 4.32.2's
`Lean/Meta/Tactic/BVDecide/Prover/Bitblast.lean:39` calls `nativeEqTrue` to check
its LRAT certificate. A plain `bv_decide` invocation therefore violates this
project's kernel-only proof policy even without a `native_decide` token.
The owner and coordinator were notified; all five bitvector solver calls were
replaced with ordinary bit-extensional proofs. The reviewer supplied the
reassembly proof in a scratch file; the owner applied it and proved the other
four half-word laws. The other inspected cones contain only `propext`,
`Classical.choice` and/or `Quot.sound`; some choice dependencies enter through
the extensional finite-container implementation, rather than semantic axioms.

The corrected proof snapshot has SHA256
`fe41b5689bde791fee182f4c575394964fda1db6e20d78f173ec67c301ca6a82`;
reviewed Defs has SHA256
`c3ffdedf33872f26d8aae6a1e015647c669d698ffdf0165c4aea6a45248b7120`.
An independent compilation of `/tmp/xv6-lean-research/VirtioReviewProofsFixed.lean`
plus `#print axioms` for all 56 public theorems passes. Every cone contains only
`propext`, `Classical.choice` and/or `Quot.sound`, with three empty cones. No
native-generated axioms remain. No owned production file was edited directly by
this reviewer.

One initially suggested documentation correction was withdrawn after checking
executable source: the record comments still call inflight/taken values ring
positions, but `virtio_pop` at 1516–1520 inserts `avail_ring_at ... v_seen`, and
`req_from`/capture/completion consume that value as a descriptor head. The
implementation's descriptor-head description is correct; only `v_seen` is an
available-ring position. Future DMA work must follow these executable rules,
not the stale comment vocabulary.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
