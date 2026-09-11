# Shared KPT hit composition: independent peer review

Reviewer: OpenAI Codex subagent `lean_logic_audit`, independently reviewing
six coordinator-authored modules: `KptHitDefs`, `Spec`, `Pure`, `Rules`,
`Proofs` and `Link`. Result: **PASS for the stated native hit-program scope**.
No implementation correction was needed. This review read every declaration
and proof in all six modules, the actual generated hit program, and the
relevant source contracts and supporting factor/refresh proofs.

`program` is the actual supervisor `translate_TLB_hit 39`, at the real VPN
hash index and an explicitly resident source walk entry. The raw factor
preserves permission failure and all A/D results. Concrete supported access
and kernel leaf permission discharge the permission check. The update uses
the cached entry's actual leaf address, rather than recomputing an address
from a presumed active root. Raw upper flags and global bits remain in that
entry; independently stale cached and reference A/D values are allowed.

The six-cell footprint splits into the existing five-cell A/D footprint and
one full TLB cell. The latter is framed across the native shared update and
rejoined before executing the actual resume. The resume plan performs the
real TLB read/write only for a successful `Some` response. Its returned PPN
and PBMT come from the original cached entry, as in the generated program;
canonical equality establishes that this remains the required mapping.
Cached success and disabled error leave the TLB untouched. The resource fold
restores exactly the resulting six-cell footprint without duplicating owned
register cells or requiring a caller-supplied memory-remainder WP.

All four A/D branches are covered with their exact zero/zero/one/two memory
guards. The branch facts are consumed inside those guards. Reread-nochange
retains its actual snapshot reservation, while completed write clears it and
returns its authored history/view receipt. The native link constructs the A/D
specification, so the intermediate dependency parameter in `wp_hit` is fully
discharged. The final continuation is an ordinary compositional WP argument.
No additional result, memory response or invariant-restoration premise is
introduced.

The pure coherence proof first derives an A/D variant from the returned
canonical equality, then applies the existing exact resident-slot refresh
law. Other slots, including hash collisions, are preserved. The invariant
and canonical snapshot clients are returned unchanged even if the physical
shared tree has been updated. The proof does not equate the current physical
leaf with the stale cached word.

Source checks: pinned generated `Vmem.lean` lines 448–474; `HartSTrans.v`
`swp_translate_hit_ex` from line 719 and its cached/update proof;
`HartSKpt.v` lines 1189–1225; `PtTree.v` lines 1693–1708 and 2286–2320.
The Lean contract also retains the ADUE-disabled error branch, whereas the
source caller specializes ADUE to enabled. The source high-level theorem
includes lookup/dispatch; this module deliberately proves the actual hit
subprogram given a resident entry and coherent vector. It does not claim
complete `translate`, two-tree SATP switching, initial KPT publication,
kernel boot reachability or a formal cross-prover equivalence.

Independent validation: `Xv6.Kernel.KptHitLink` rebuilt successfully at 817
jobs. A fresh physical-origin audit checked all **66 declarations** in all
six modules, including private declarations and every type, opaque proof
body and constructor dependency. Only `propext`, `Classical.choice` and
`Quot.sound` occur; no unsafe or partial semantic dependency, zero exclusions.
SHA256 checks confirmed all six reviewed files remained unchanged throughout
review, build and audit. Evidence is retained under
`/tmp/xv6-lean-research/KptHitPeerAudit.lean`, `kpt-hit-peer-audit.log`,
`kpt-hit-peer-build.log` and `kpt-hit-peer-before.sha256`.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
