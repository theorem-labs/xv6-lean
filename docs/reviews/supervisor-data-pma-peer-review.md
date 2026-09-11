# Supervisor ordinary-data PMA plans: independent review

PASS for the declared finite-plan scope. Codex independently read the
coordinator-authored SupervisorDataPmaDefs, Spec, Proofs and Link in full,
plus the design, actual generated PMA/memory functions and native
RegisterPlan constructors. No correction or owner-file edit was required.

Defs selects precisely Load.Data or Store.Data, PBMT_PMA and a false
reservation/conditional flag. Grant inspects exactly the readable or
writable attribute of override_PMA on the actual matched region. The
Specs retain actual matching_pma_region and physical-alignment premises,
and a fractional pma_regions cell belonging to the supplied footprint.
The result is exactly Ok {splittable=CannotSplit, granule_size_exp=0}, with
the complete original dependent register file unchanged.

The proof unfolds actual Mem.pmaCheck (Mem.lean:262–382). Its single owned
read obtains rs.pma_regions; matching selects the real region, the ordinary
access branch preserves and resolves the nonconditional assertion, and
Grant resolves only the consumed permission field. It then executes
is_mag_applicable_access rather than treating it as a granted event. In
Pma.lean:349–416, ordinary data returns the width≤xlen_bytes boolean; the
explicit alignment fact selects CannotSplit regardless of that boolean or
any arbitrary MAG attributes. The early-return/Except wrappers are
composed through proved finite binds, with no evaluated-state oracle.

priority_plan unfolds actual Mem.check_pma_with_pmp_priority:393–401.
The successful PMA arm returns its access information directly. It makes
no PMP read; the PMP priority branch is only on PMA error. Nothing here
proves a PMP grant, translation, RAM/MMIO selection, data result or actual
memory event. The unchanged register-only result is structurally witnessed
by native RegisterPlan.read and pure constructors; the helper bind laws
retain the real Free program and exact result/file equalities.

The source correspondence is the aligned PMA peel in
iris/RiscvExtras.v:1015–1127: pma_ok_aligned,
exec_mag_pma_check_aligned, ordinary load/store applicability, true assert,
and pma_ok_peel. The Lean API uses the generated Nat width, whereas the
Rocq source parameter is Z. This review does not claim signed-width
representation equivalence or that arbitrary Nat widths are valid machine
accesses. The two statements are exactly the generated PMA calls under
matching/alignment premises; the design explicitly preserves that limit.
It does not generalize conditional, atomic, vector, fetch or PTE accesses.

Independent verification:

- Build MachCSL.Logic.SupervisorDataPmaLink:447 jobs, success.
- Strict audit:62 declarations from all four physical modules, including
  private/generated declarations. Exporting disabled; collectAxioms for
  every root and traversal of all types, opaque bodies (allowOpaque=true),
  and inductive constructors. Only propext, Classical.choice and Quot.sound;
  no unsafe/partial dependency; zero exclusions.
- Driver /tmp/xv6-lean-research/SupervisorDataPmaPeerAudit.lean; logs
  supervisor-data-pma-peer-{build,audit}.log in the same directory.

Source pin fa7f0a01c4b40489fac8ad303f079c2dfc7a1476. Review covers these
four frozen modules and their actual dependencies, not a native full data
word rule, source push_off instruction WP or function correctness.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
