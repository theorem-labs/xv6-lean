# Shared exclusive leaf event

All four modules Defs, Spec, Proofs and Link compile. The approved two-field
contract is implemented by `actual`, and the final `nativeSpec` and
`registrySpec` discharge the ownership and native machine dependencies.
No caller supplies a slot, publication bound, boot credential, physical read
result, restoration callback or successful program theorem. No new camera
or runtime name is introduced.

`heap_slot_read` derives the current eight-byte physical read from the full
heap interpretation and the native slot's byte ownership. It uses exact
finite-map decoding and byte agreement, including each of the eight bytes.
The result is pure, allowing the current-tree accessor to retain and restore
the original slot; no fractional or timestamp resource is upgraded.

`current` opens the shared invariant under the explicit namespace-mask
inclusion. Actual snapshot agreement transports the complete pure Maps path
to the current tree, including its raw upper words and unchanged leaf slot
address. It extracts the current full kernel-tier leaf, derives the current
read and canonical equality, and restores the complete tree and mapping
body through the actual returned wand. It returns exactly the original
readBundle, already-advanced TSO interpretation, log-top receipt and both
persistent clients. No unrelated field or authority is reconstructed from
an assumed preservation property.

`wp_read` invokes the real native exclusive eight-byte RAM rule with the
complete request and residual continuation. Its pure premises retain the
complete Maps path, exact leaf address, nondevice guard and exclusive access
kind. The native rule advances the live hart to the actual log top before
calling the implemented premise. Only then does `current` open and close
the shared invariant; closure completes before the top-to-empty mask
transition and the single event guard.

Success returns the exact snapshot reservation, genuine view receipt,
canonical leaf fact, both persistent clients and the actual
`continuation (Ok (word, none))` WP. The underlying native rule preserves the
actual overlap branch: the same event remains pending while its old own
reservation is cleared. It supports arbitrarily many retries through guarded
Löb and retains the existing dead-generation case. No successful result,
fairness or termination is claimed on that blocked branch. Error responses
are not fabricated or silently replaced: the full continuation remains an
argument, and the proved RAM/exclusive event semantics selects its actual
success arm. Generated prefix and PTE/A-D wrapper factorization remain
separate follow-up composition.

Source mapping, paper pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:

- `HartSKpt.v:210–250`, `kpt_open_slots` and `read_bytes_of_slot`: reopen the
  current shared tree, derive pure current-memory facts and close it.
- `PtTree.v:1431–1517`: source full path extraction and reassembly, via the
  separately checked native Ownership implementation.
- `HartEvents.v:398` (`wp_hart_ram_read_excl`) and
  `PtTreeAdue.v:1013` (`swp_checked_mem_read_pte8_excl_ex`):
  source current-memory read, overlap reservation clearing and actual result.
  These operational alternatives are provided by the existing native
  `MemoryExclusiveWP.wp_exclusive`, not redefined by this layer.

Validation: `PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build Xv6.Kernel.KptExclusiveEventLink`
passed all 727 jobs. Fresh physical-origin audit:
`/tmp/xv6-lean-research/KptExclusiveEventOwnerAudit.lean`; raw build and audit
logs are `kpt-exclusive-event-owner-build.log` and
`kpt-exclusive-event-owner-audit.log` in that directory. The audit follows
every type, opaque proof body and inductive constructor. All 22 physical
declarations across four modules passed: only `propext`, `Classical.choice`,
and `Quot.sound`, with zero exclusions and no unsafe or partial dependencies.

This layer proves one shared exclusive leaf event. Conditional A/D commit,
full shared walk, TLB coherence, publication from actual boot ownership and
translated function correctness remain separate obligations.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
