# Full shared-KPT mycpu function

FROZEN: all twelve pure contracts and the native function contract are
proved in seven modules: Defs, Spec, State, Pure, Guards, Proofs and Link.
`nativePureSpec`, `nativeSpec` and `registrySpec` are actual constructors;
there is no remaining component interface premise.

The exact actual fourteen-cycle composition retains arbitrary original
GPRs, scratch-word contents, clock successors and reservation. Internal Phase
bookkeeping derives each indexed PC/StackReady and the two stored values;
the final result restores the saved GPRs/SP and computes the real CPU address.
The fixed virtual save anchor is entrySP−16 throughout.

The public rule owns the same fifty-cell packet, folded residue, code,
running context, virtual pair and literal frame, with only the genuine
returned-cycle continuation as a WP premise. It returns all fourteen indexed
fetch/body receipt bundles, exact restored values and cleared reservation.
No per-step oracle, Bare configuration, physical stack substitute or hidden
SATP/PMP/TLB duplication is introduced.

Source capability opening/closing belongs to the separate MycpuKptEntry
adapter. Its explicit extra PMA requirement, source callable-JAL wrapper,
interrupt-enabled/migration case and resource reachability are separate.

Build: `python3 tools/lake.py build Xv6.Kernel.MycpuKptLink` passed 1,155 jobs
(State 8.7 s, Pure 2.0 s, Guards 1.3 s, Proofs 1.3 s, Link 1.1 s).
Final build log: `/tmp/xv6-lean-research/mycpu-kpt-native2.log`.
Fresh audit checked all 202 declarations in seven physical modules through
types, opaque values and constructor dependencies: standard propext,
Classical.choice and Quot.sound only, no unsafe/partial dependency, and zero
exclusions. Audit script/log: `MycpuKptAudit.lean` and `mycpu-kpt-audit.log`
under the same research directory. Recursive receipts are noncomputable;
no compiler companion exemption was added.
Exact mapping and proposed proof boundaries:
`docs/design/mycpu-kpt-boundary.md`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
