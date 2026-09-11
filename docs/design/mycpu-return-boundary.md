# Actual mycpu return-body boundary

Implemented boundary by the Codex Lean-logic agent. This is an execution-body
prerequisite for the source interrupts-off `mycpu` function, not a fetched
function WP or an enabled-interrupt handler contract. The coordinator approved this boundary; the four MycpuReturn modules are
now built and audited. See `Xv6/Kernel/MycpuReturnSTATUS.md` for the completed
contracts and validation.

## Source and concrete instruction

The source pin is xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`.
I read the complete `ProofMycpu.v`, including its final return at lines
275–287 and function conclusion through line 317. It calls
`WpSconfCtl.wp_cret_s_sconf` (311–359), which extracts supervisor control
resources and uses `WpSconfEngine.swp_execute_JALR_ret_s` (622–680).
`RiscvExtras.v:905–950` defines and proves the basic laws of
`ret_pc v := update_vec_dec v 0 0`.

The existing image/decode certificate identifies the final actual instruction
at `0x800018d8`, index 13 of 14, encoding `0x8082`, as `C_JR (Regidx 1)`.
Its actual `ExecuteAs` target is `JALR (0, Regidx 1, Regidx 0)`.
Reuse `MycpuDecode.decoded/normalized` and prove the same actual
execute/ExecuteAs selection equality used by `MycpuScalar.body`; do not
replace a fetched instruction or assert an unproved decoder result.

The source return leaf borrows full nextPC, full privilege, full menvcfg,
discarded misa and a GPR file. The actual body only reads RA from that GPR
file. Its surrounding instruction funnel frames PC and later retires to the
new nextPC. The narrower native footprint below preserves this separation.

## Exact generated path

The checked model is the pinned generated Sail model, upstream
`23dcf8fd923eb8a1958795393d2975632aa940b2` with the repository's recorded adapter.
The relevant definitions are:

| Definition | Actual effect on the proposed source-configured path |
| --- | --- |
| `InstsEnd.execute_C_JR`, lines 17747–17748 | Pure `ExecuteAs (JALR (0, rs1, x0))` |
| `InstsEnd.execute_JALR`, 17459–17468 | ELP check; nextPC read; RA read; add zero; clear bit zero; jump; discarded x0 link write |
| `ZicfilpRegs.update_elp_state`, 242–251 | Tests actual Zicfilp enable; no ELP write when supervisor LPE is disabled |
| `PlatformConfig.currentlyEnabled`, 2634–2636 and 2677 | Zicsr is pure true; read privilege, then supervisor menvcfg for LPE |
| `PlatformConfig.get_xLPE`, 2726–2738 | Supervisor branch reads menvcfg; no mseccfg or senvcfg read on this path |
| `BaseInsts.jump_to`, 249–259 | Pure extension control check, bit-zero assertion, actual Zca check, nextPC write |
| `PlatformConfig.currentlyEnabled`, 2651–2653 | Zca uses misa.C; the eager generated read remains even if target bit one is zero |
| `AddrChecks.ext_control_check_pc`, 210–211 | Constant `none`, independent of target and platform predicates |
| `PcAccess.get_next_pc/set_next_pc`, 210–216 | Actual nextPC read/write; branch announcement and redirect callback are pure unit |
| `Regs.rX_bits/wX_bits`, 623–707 | x1 is one real register read; x0 write emits no register event and skips its write callback |

Thus the anticipated exact ordered register trace is:
`read cur_privilege; read menvcfg; read nextPC; read x1; read misa;
write nextPC target`. Every event is retained. This ordering will be proved
from the generated tree, not used as a hardware-semantics replacement.

There is no pointer-mask application in this JALR/control-check path. In
particular it does not read PMM, mstatus, satp, or a page table to form its
return target. The subsequent fetch/translation remains separate. The source
supervisor configuration does pin PMM disabled, but no extra pointer masking
or canonical-address assumption should be introduced into this body theorem.
Likewise, extension control checks and redirect/branch callbacks have their
actual pure definitions; they are not caller-supplied success assumptions.

## Proposed definitions and contracts

Own new `Xv6/Kernel/MycpuReturn{Defs,Spec,Proofs,Link}.lean` and STATUS, with
namespace `Xv6.Kernel.MycpuReturn`. Reuse existing cameras and native
`RegisterPlan`; no new capacity slot or full-register-file ownership.

Define `retPC (ra : BitVec 64) := Sail.BitVec.update ra 0 0#1`, and
`after rs := Registers.write rs .nextPC (retPC (rs .x1))`.
RA and initial nextPC are arbitrary 64-bit words. Prove `retPC` bit zero is
zero, the zero-immediate JALR target identity, and all non-nextPC fields of
`after` unchanged. No two/four-byte alignment or canonical-address premise
on RA is required: the instruction clears its low bit and source misa.C
permits the resulting two-byte alignment.

A `Shares` record supplies independent RA, privilege, menvcfg and misa
fractions. The minimal `footprint shares` has exactly five cells:

```
[(nextPC, own 1), (x1, shares.ra),
 (cur_privilege, shares.privilege), (menvcfg, shares.menvcfg),
 (misa, shares.misa)]
```

A low-level `Config rs` requires only actual privilege Supervisor,
`bool_bit_backwards (_get_MEnvcfg_LPE (rs menvcfg)) = false`, and
`_get_Misa_C (rs misa) = 1`. Other config bits remain arbitrary. A separate
source-config corollary derives this from
`rs cur_privilege = Supervisor`, `rs menvcfg = 0xA000000000000000`, and
`rs misa = 0x800000000014112D` (`RiscvFetchExec.v:224–225`). MENVCFG_S enables
ADUE and STCE; PBMTE and LPE are zero. Its actual value is retained in this
source specialization, not replaced by zero or a machine-reset snapshot.

The constructed pure theorem will have the shape:

```
body_plan [Platform] (shares) (rs) (config : Config rs) :
  RegisterPlan.Returns (footprint shares) rs body
    (.Retire_Success ()) (after rs)
```

Here `body` runs the actual decoded `C_JR` and its actual `ExecuteAs` body,
and the theorem supplies its plan internally. Auxiliary plans should factor
Zicfilp-disabled, Zca-enabled, and jump-to-low-bit-cleared-target to avoid
whole-generated-model reduction. Prove the x0 link write is pure while
retaining the preceding link-address read.

The native `Spec` and its constructed proof expose:

```
generationCertificate -∗ cells rs shares -∗
  (cells (after rs) shares -∗ WP (.hart gen cpu (k (.Retire_Success ())))) -∗
  WP (.hart gen cpu (body >>= k))
```

This uses the existing native register fold, so actual generation changes and
every interleaving between events are retained. The public theorem has no
supplied plan, success fact, software continuation correctness oracle, or
whole-step correctness premise. The WP continuation is the ordinary logical
continuation of this body. No extra later is invented beyond the native fold.

Add a six-cell PC-framing corollary with arbitrary fractional PC and exact
unchanged `rs PC`, to fit the source `HPC` frame and later retirement. A source
fraction specialization uses full nextPC/privilege/menvcfg/RA and discarded
misa, without weakening full resources already held elsewhere. PC itself is
not read or written by this body, and will only change in the separately
proved actual retirement postlude. Reservation ownership, stack, contexts,
other GPRs and memory may be framed; no instruction-body reservation update
is claimed.

## Limits and validation

This leaves instruction fetch, physical/virtual target validity, decode
configuration ownership composition, setup/retirement/clock composition,
SIE capability and stack/VA resources, and the complete mycpu specification
for subsequent work. It neither allocates nor duplicates source `sconf`,
`pc_is`, `sie_cap`, or a whole GPR resource. The concrete RA index is x1,
so the source `SrcOk` concern about a TP-derived return target is absent;
there is no assertion of arbitrary enabled-handler hart migration.

Validate symbolic arbitrary RA and nextPC, both possible target bit-one
values, exact C_JR/ExecuteAs equality, unchanged non-nextPC fields, source
configuration specialization, and the native partial-footprint fold by Lean
kernel proofs. Use fresh physical-origin all-file audits with opaque bodies,
types and constructors, allowing only the standard three foundational
axioms. No native decision axioms or generated-model edits. Exact model to
Rocq correspondence remains the repository's separately documented boundary.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
