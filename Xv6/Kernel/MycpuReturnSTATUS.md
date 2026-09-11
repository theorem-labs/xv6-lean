# Actual mycpu return-body native WP

Implemented and frozen in `MycpuReturn{Defs,Spec,Proofs,Link}.lean`.
`body` executes the actual final compressed instruction, index 13 in the
existing image/decode certificate, and follows its generated `ExecuteAs`
to `JALR (0, x1, x0)`. `body_eq` is a kernel-checked definitional equality.
The instruction is at `0x800018d8`, encoding `0x8082`.

The native `wp_return` needs only full nextPC plus four independently
fractional cells: RA/x1, privilege, menvcfg, and misa. Its configuration
requires Supervisor, LPE disabled, and misa.C set. All other register values,
RA bits, initial nextPC and unrelated configuration bits are arbitrary.
`source_config`, `source_body_plan`, and `wp_source` specialize to the exact
source constants MENVCFG_S `0xa000000000000000` and MISA_C
`0x800000000014112d`. The source shares are full RA/privilege/menvcfg/nextPC
and discarded misa. No new resource camera or full-register-file assertion
is introduced.

The checked register-event sequence is privilege read, menvcfg read,
nextPC read, x1 read, misa read, then nextPC write. The generated Zicfilp
check remains; its supervisor LPE-zero result makes the ELP write branch
unreachable. The generated compressed-alignment check remains, including
the eager misa read regardless of target bit one. The preceding nextPC
link-address read remains even though the link is discarded. `zero_link`
checks that the actual x0 write emits no register event or write callback.
Branch announcement and redirect callback use their actual pure definitions.

The only changed register is `nextPC := retPC RA`, where `retPC` is the actual
64-bit bit-zero update. `retPC_aligned` and `retPC_jalr` hold for arbitrary
RA, and require no aligned or canonical target premise. Pointer masking and
translation are not executed by this generated JALR path. `after_other`
proves unchanged non-nextPC fields. `pc_body_plan`/`wp_return_pc` add an
arbitrary fractional PC cell and return it unchanged; `after_PC` states the
corresponding value equality. PC retirement is separate.

The public Spec is constructed from `RegisterPlan.fold` and the proved
actual body plan. It has no caller-supplied plan, success result, subordinate
WP, or software contract. The continuation is the actual free-program
continuation. Register events are not collapsed atomically, and the existing
native generation/dead-thread rules handle interleavings and power changes.

Source mapping at xv6iris `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:

| Lean theorem/definition | Source |
| --- | --- |
| `retPC`, `retPC_jalr`, `retPC_aligned` | `RiscvExtras.v:905–950` |
| `body_plan`, source specialization | `WpSconfEngine.v:622–680`, `swp_execute_JALR_ret_s` |
| Five-cell footprint / PC frame | Source four-cell jump control frame at `WpSconfEngine.v:306–362`, RA read from the source GPR file; `WpSconfCtl.v:311–359` frames PC |
| Actual final mycpu instruction | `ProofMycpu.v:275–287`, function proof through 317; existing `MycpuDecode` image certificates |
| Exact source configuration | `RiscvFetchExec.v:224–225`, `IntrDefs.v:595–623`, `WpSconfEngine.v:1155–1174` |

Generated path: `InstsEnd.lean:17459–17468,17747–17748`,
`ZicfilpRegs.lean:242–251`, `PlatformConfig.lean:2634–2636,2651–2653,2726–2738`,
`BaseInsts.lean:249–259`, `PcAccess.lean:210–216`, `Regs.lean:623–707`,
`AddrChecks.lean:210–211`, and pure callbacks in `Callbacks/Common0`.

Validation: `python3 tools/lake.py build Xv6.Kernel.MycpuReturnLink` passed
504 jobs; Proofs took 1.1 seconds and Link 878 ms. The fresh physical-origin
audit checked all **88 declarations** in all four modules, private helpers
included, following types, opaque proof bodies, and inductive constructors.
Only `propext`, `Classical.choice`, and `Quot.sound` occur; no unsafe/partial
dependency and zero excluded runtime companions. Evidence:
`/tmp/xv6-lean-research/MycpuReturnAudit.lean`, `mycpu-return-audit.log`, and
`mycpu-return-build.log`. No sorry, custom axiom, native decision tactic,
generated-model edit, or existing implementation-file edit was used.

This is the final instruction's execution-body prerequisite, not a fetched
function WP. Fetch, decode-resource composition, target translation and
validity, setup/retirement/clock composition, source SIE/stack/VA context,
and complete mycpu correctness remain separate. This does not implement an
enabled-handler contract or prove hart migration. Whole generated-model to
Rocq correspondence remains the repository's separately recorded limitation.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
