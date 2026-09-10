# Independent Virtio DMA review

Review outcome: no executable mismatch found in the reviewed pure DMA layer
against `iris/VirtioModel.v` at paper commit
`fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`. This extends the earlier state/MMIO/
sector review in `virtio-review.md`; it does not certify the unported driver or
Iris invariants, or a Rocq/Lean finite-map representation theorem.

Reviewed frozen source hashes:

- `MachCSL/Devices/Virtio/Dma.lean`:
  `6eb30cce05baf1fd4adf23f485342e995348b7e96ec2ba5a7d5a6f9849729d33`.
- `MachCSL/Devices/Virtio/DmaProofs.lean`:
  `0ec9c79b28e88b94be55db6ef769e9699a1b890eb53632c8d4f72542c6d0038f`.

Read source definitions and matched the following behavior:

- `VirtioModel.v:682–694`, `RiscvModelBytes.v:45–48,108–111,174–180,217–220`:
  byte reads, writes, and address arithmetic. `pa_off` clips negative integer
  displacements to zero before 64-bit modular addition. Byte-list writes use a
  right fold, preserving the first byte on wraparound aliases. Assembly uses
  arbitrary-precision integers and all requested bytes before conversion to the
  requested bit width; no hidden 64-bit accumulator truncation.
- `VirtioModel.v:1021–1051`: total bus views extend all present partial-memory
  bytes and leave absent bytes arbitrary. `view_bytes_read` and `view_word_read`
  prove the key ownership/read bridge. `empty_memory_has_distinct_views` supplies
  a checked witness that missing bytes are not defaulted.
- `VirtioModel.v:1108–1183`: descriptor decoding and `chain_from` preserve exactly
  three descriptors and their index/NEXT conditions. No distinctness, direction,
  header-length, or status-length restriction was added. Only pop reads the
  available ring; later phases retain the descriptor head. Several upstream
  comments still call these values positions; the executable definitions govern.
- `VirtioModel.v:1202–1250,1279–1345`: modular ring distance, used-length derivation,
  used-ring writes, write payloads, sector counts and absolute cache keys.
  Used length depends on the writable flag even for unknown request types and
  wraps at 32 bits. Used head, used length, then used index are composed in that
  order; later writes win on aliases between these fields.
- `VirtioModel.v:1347–1499`: cache sets, span, and completion. Finite set/domain
  disjointness is justified by `cache_disjoint_spec`. `cache_overlay_lookup`
  proves that fresh captured sectors have the source's left-biased union
  precedence. `cache_view_read` proves the uncached-span/durable-read bridge,
  including a partial final sector. Status insertion wins over the used-ring
  map, then a READ payload wins over both if its buffer aliases them. Neither
  completion nor capture updates the durable disk. Completion preserves cache
  and clears the capture latch only when the completing head owns it.
- `VirtioModel.v:1511–1886`: pop, serve, completion gates, capture, drain, stalled.
  OUT requires its own capture latch plus either write-back mode or uncached
  touched sectors. FLUSH requires an empty cache. READ and unknown types require
  write-back mode or uncached touched sectors. Capture additionally requires an
  empty latch and stores every payload sector before completion. Drains require
  only a present cache entry: no queue-liveness, RAM-view, type, or latch gate.
  Drains write the whole entry at signed integer offset `512 * sector`, then
  delete that key. Malformed in-flight chains set `virtio_stalled`; the machine
  caller must preserve the source's wild-write rule rather than silently stop.

The cache carrier intentionally stores arbitrary lists. A maximum 512-byte
entry is a future reachable-state invariant; imposing that bound on raw
operational transitions would change the source. Likewise the disk is a total
integer-indexed function, including negative offsets. The RAM representation is
an extensional partial function over 64-bit addresses. Source `gmap` lookup and
union behavior have been matched here; a formal cross-language representation
bridge is not established by this review.

Validation:

```
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Devices.Virtio.DmaProofs
```

The module build passed. An enforced `Lean.collectAxioms` audit passed for all
256 theorems in `MachCSL.Devices.Virtio` imported by this module, including
compiler-generated structure theorems and the prior layer. Every transitive
axiom was among `propext`, `Classical.choice`, `Quot.sound`; no native decision
axiom was present. The DMA file contains 61 public handwritten theorems.

Eight additional ordinary-kernel scratch checks passed: negative `pa_off`, a
nine-byte/72-bit all-ones read, a negative bit-mask flag, READ data/status/index
aliasing, unknown-type status/index aliasing, used-length overflow, a negative
sector drain, and that drain's disabled queue state. The arbitrary-width and
aliasing cases specifically exercise behaviors that narrower examples would
miss. No production files were changed during this review.

Scratch audit drivers and logs are under `/tmp/xv6-lean-research/`:
`VirtioDmaAudit.lean`, `virtio-dma-review-axioms.log`,
`virtio-dma-review-build.log`, `VirtioDmaEdges.lean`,
`virtio-dma-edge-review.log`. These are temporary review artifacts, not required
repository build inputs.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
