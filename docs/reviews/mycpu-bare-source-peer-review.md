# Mycpu identity/Bare source branch — independent review

PASS. The independent Codex subagent read all seven frozen Lean modules,
STATUS/design, full pinned `SpecMycpu.v` and `ProofMycpu.v`, and the exact
`SRegime.v:823–861`, `TsoCtx.v:628–641,845–860`, and
`StackOwn.v:136–175,271–303` resource definitions. No implementation change
was requested or made.

The theorem is the opened identity-tier **Bare arm**, accompanied by the
same-hart boot-PMA ownership and source text. It does not infer Bare from
identity tier. The three SATP/PMP values are obtained from their actual
owned existential cells; patching their projections does not claim values
for any unowned physical register. The resource equivalence accounts for
all fifty source cells plus precisely these three, with no TLB cell.

The two scratch words come from the exact stack split under `2 ≤ available`.
Their identity physical addresses follow from retained mapping/tier claims.
Each closing wand quantifies over the newly stored word, preserving the
original mapping while accepting the actual updated byte timestamps. The
tail, same running context, pending/stvec resources, timer, tier witness,
hardware certificate, status ties, off token, full GPR ownership and literal
frame survive. Closing restores the original full stack count and source
capability; it does not require the scratch words to retain their old values.

The sparse source-map theorem covers all 34 bytes used by real instruction
fetch, including the final two lookahead bytes. Native text extraction
produces the corresponding discarded physical byte/pristine window from
the existing persistent identity text. There is no default-byte premise or
caller-provided physical-code/stack-word/decoder/body-success oracle.

The Link internally supplies `MycpuOff.nativeSpec`; the public function rule
therefore composes the existing actual fourteen-cycle proof. Its returned
Result supplies callee-saved preservation and a0 from the same hart's TP,
restored SP and the exact return target. Actual clock-successor continuation
is retained. General PMA, identity-tier KPT dispatch, source entry
inhabitation and boot reachability are correctly excluded from this branch.

Fresh validation passed:

- `python3 tools/lake.py build Xv6.Kernel.MycpuBareSourceLink`: 1,031 jobs.
- `MycpuBareSourcePeerAudit.lean`: **120 physical-origin declarations** from
  all seven modules, with exporting disabled to include private constants;
  complete type, opaque-value and constructor traversal; only `propext`,
  `Classical.choice`, `Quot.sound`; no unsafe/partial or Initial dependency,
  zero exclusions.

Evidence under `/tmp/xv6-lean-research`: `mycpu-bare-source-peer-build.log`,
`mycpu-bare-source-peer-audit.log`, `MycpuBareSourcePeerAudit.lean`.

| Frozen module | SHA-256 |
| --- | --- |
| `Xv6/Kernel/MycpuBareSourceDefs.lean` | `a16ba478b24929a643fb8f70fbf665a22157d3c10190aa2f4da18ee6fc99b804` |
| `Xv6/Kernel/MycpuBareSourceSpec.lean` | `e35665354f2f6f2f5f7fa07900ac334841109af88e9f2dd96e5f14c2914afe20` |
| `Xv6/Kernel/MycpuBareSourcePure.lean` | `01352134e31b2c7826dfb2447d0991476301bfdc912d792758e868e27ba8bca2` |
| `Xv6/Kernel/MycpuBareSourceResources.lean` | `a866fcf315ab8c62416baf0e1aa53b8059350fde47de650a1511429af29a1900` |
| `Xv6/Kernel/MycpuBareSourceEntry.lean` | `8e98f92c8bf566237c87b94c154109377488e9c07caca7dd467e369b91cbaf4d` |
| `Xv6/Kernel/MycpuBareSourceProofs.lean` | `51c8166e5e353f975ab8c13daa6c014e9298ad393d5c051f4483043eef949aac` |
| `Xv6/Kernel/MycpuBareSourceLink.lean` | `a5bc7bd9897d23fca42ab6d116dd359db0ea9c4b4bf48815f285a094f6426c26` |

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
