# PLIC component status

Source: [`iris/DevModel.v`](https://github.com/mit-pdos/xv6iris/blob/fa7f0a01c4b40489fac8ad303f079c2dfc7a1476/iris/DevModel.v),
`xv6iris` tag `arxiv-v1`, commit `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
The complete PLIC section is lines 752–945, geometry is lines 52–64, and the
power-on state is lines 1136–1138. There are **no PLIC lemmas in that source
section**. `Proofs.lean` adds properties of the transcription rather than
presenting unrelated source lemmas as ported.

## Source mapping

All Lean names below are in `MachCSL.Devices.Plic`.

| Rocq | Lean |
| --- | --- |
| `plic_state`, `PlicState` | `State`, `State.mk` |
| `p_prio`, `p_pending`, `p_claimed`, `p_enable`, `p_thresh` | `State.prio`, `.pending`, `.claimed`, `.enable`, `.thresh` |
| `plic_base`, `plic_size`, `dev_ncpu` | `base`, `size`, `nCpu` |
| `uart_irq_id`, `virtio_irq_id` | `uartIrqId`, `virtioIrqId` |
| `plic_nsrc`, `plic_nwords`, `plic_nctx` | `nSrc`, `nWords`, `nCtx` |
| `plic_mctx`, `plic_sctx` | `mCtx`, `sCtx` |
| `plic_src_word`, `plic_src_bit` | `srcWord`, `srcBit` |
| `nupd`, `hupd`, `wupd` | `nupd`, `hupd`, `wupd` |
| `plic_enabled`, `plic_cand`, `plic_better` | `enabled`, `cand`, `better` |
| `plic_srcs`, `plic_best` | `srcs`, `best` (with its fold body named `select`) |
| `plic_claim`, `plic_complete`, `plic_eip` | `claim`, `complete`, `eip` |
| `plic_pending_word` | `pendingWord` |
| `plic_prio_src`, `plic_pending_widx`, `plic_enable_ctx` | `prioSrc`, `pendingWidx`, `enableCtx` |
| `plic_thresh_ctx`, `plic_claim_ctx` | `threshCtx`, `claimCtx` |
| `plic_read`, `plic_write`, `plic_latch` | `read`, `write`, `latch` |
| `plic0_state` | `initial` |

## Representation and exact scope

Both source natural-number index types (`N` and `nat`) map to unrestricted
`Nat`. State fields remain total functions on those indices; no arrays, `Fin`
indices or domain invariants restrict arbitrary states. The complete candidate
scan is the ordered list 1 through 95. Both contexts of each of eight harts
remain present. Candidate visibility requires pending, enabled, and priority
strictly above threshold. Selection uses the source's left fold, higher priority
first and smaller ID on equal priority.

MMIO offsets remain `Int`, with Euclidean division/modulus and the source
signed guards. Word values are `BitVec 32`; unsigned comparisons use `toNat`.
The nonnegative source bit index `Z.of_N i mod 32` is represented by `i % 32`.
`pendingWord` folds right over the same 32 bit positions, performing natural
shift/or before conversion to a 32-bit word. These are explicit numeric
representation choices, not an imported proof that Rocq's `Z`/`N`/`bv` libraries
correspond to Lean's implementations.

Several source details are intentionally retained:

- `latch` has no source-range guard. Board wiring must choose the interrupt ID.
- Completion alone checks IDs 1 through 95; invalid IDs preserve state.
- Claim clears pending and sets claimed; completion clears claimed without
  changing pending. Candidate visibility itself does not test claimed.
- Source zero is excluded from arbitration and its priority MMIO register reads
  zero and ignores writes. Arbitrary pending word zero can still expose bit zero;
  enable-word writes retain every bit, including bit zero. The source does not
  normalize arbitrary state to its intended reachable-state invariant.
- Decoder precedence is priority, pending, enable, threshold, claim. Only claim
  reads change state. Pending writes are accepted without changing state.
- Reserved offsets, misaligned offsets and addresses outside decoded registers
  return `none`. Negative offsets are not truncated into valid registers.

The component does not instantiate UART/disk IRQ wiring, the bus's access-width
checks, CPU pending-interrupt bits, concurrent device transitions, a Sail handler,
or a MachCSL device invariant. Those are fabric/machine/proof-layer work.

## Checked laws

`Proofs.lean` establishes:

- Pointwise updates: `nupd_same`, `nupd_other`, `hupd_same`, `wupd_same`,
  `wupd_other`.
- Full source range and comparison properties: `mem_srcs`, `cand_iff`,
  `cand_false_of_threshold`, `better_iff`, `better_irrefl`, `better_tie`,
  `better_asymm`, `better_trans`.
- Fold selection: `select_eq_none`, `fold_eq_none`,
  `best_none_iff_eip_false`, `select_some_source`, `fold_some_source`,
  `best_some_valid`, `fold_preserves_bound`, `fold_dominates_candidates`,
  `best_optimal`, `best_some_threshold`. `best_optimal` proves that every
  candidate's priority is at most the winner's and equal-priority candidates
  have IDs at least the winner's.
- Claim/completion/gateway: `claim_none`, `claim_no_interrupt`, `claim_some`,
  `claim_clears_pending`, `claim_marks_claimed`, `claim_preserves_other`,
  `claim_id_exact`, `complete_valid`, `complete_invalid`, `complete_pending`,
  `latch_iff`, `latch_pending`, `latch_blocked_pending`, `latch_blocked_claimed`,
  `claim_blocks_latch`, `completion_allows_relatch`.
- Register decoding: `prioSrc_bounds`, `pendingWidx_bounds`, `enableCtx_bounds`,
  `threshCtx_bounds`, `claimCtx_bounds`, `read_source_zero`, `write_source_zero`,
  `read_none_iff`, `write_none_iff`, `read_none_iff_write_none`, `negative_offset`,
  `write_pending_readonly`.
- Power-on behavior: `initial_cand`, `initial_eip`, `initial_best`,
  `initial_claim`, `initial_pendingWord`.

Validation uses `python3 tools/lake.py build MachCSL.Devices.Plic.Proofs`
on Lean 4.32.2. An aggregate compiled audit checked all 112 theorem declarations
(including generated equation theorems); the union of their axioms is only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, custom axiom, `native_decide`, or unbounded host
execution is used to prove these laws. A successful build checks the Lean
transcription and its stated properties; full cross-prover and system
correspondence is still outstanding.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
