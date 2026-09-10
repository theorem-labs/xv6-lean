# Generated cold-boot witness review

The Lean witness runs the actual generated `bootProgram` from the total
`zeroRegisters` file, for arbitrary 64-bit reset vector and hart ID. It does not
replace boot execution with a literal post-state or restrict the machine's
permitted initial register files to this witness.

Source mapping at `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`:

- `iris/ArchReset.v:233–274`: `board_wired`, `board_regs`, `board_init`,
  `boot_prog`; Lean `BootProgram.lean` explicitly parameterizes the reset vector
  for the shared JAL/xv6 machine and uses the actual generated reset and firmware.
- `iris/ArchReset.v:69–140`: the reset chain and its parameterized platform hook.
  This certificate concerns the repository's generated Lean realization; a
  general Rocq/Lean Sail interpreter correspondence remains a separate obligation.
- `models/riscv/LeanPaperStock/SysControl.lean:748–773`: actual `reset_misa`.
  `ColdBootFacts.misaResetValue` records its eleven updates in the same order,
  starting from the board-written MXL value. Kernel conversion proves the full
  boot's MISA projection equals this expression. A separate proof-producing
  `cbv` certificate evaluates the expression to `0x800000000014112d`.
- Generated `reset_sys` writes both PC and nextPC from `pc_reset_address`;
  `boot_pc` proves both actual projections equal the arbitrary supplied vector.

`ColdBoot.lean` exports `boot_succeeds`, `bootResult_eq`, and `boot_run`.
The last theorem uses the proved `registerRun_sound` theorem to obtain a real
`Run` under every device bus, with unchanged RAM and devices. The success
certificate uses fuel 10000; it proves this bound suffices and does not alter the
unbounded relational semantics. `bootRegisters` extracts the successful result
using this proof. A generic lemma for `Option (Unit × α)` keeps result extraction
independent of expensive boot unfolding.

`ColdBootFacts.lean` exports the original Option-valued `boot_pc` / `boot_misa`
and direct `bootRegisters_pc` / `bootRegisters_misa` projections. The successful
run and every requested projection are preserved. This is an existence witness
from Lean's all-default dependent register file; it does not claim that this
file is definitionally identical to Rocq's compiled `init_regstate`, nor does it
prove every reset postcondition for arbitrary initial register files.

Validation (Lean 4.32.2, repository's two-thread wrapper):

```
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Machine.ColdBoot
PATH=/data/jason/.elan/bin:$PATH python3 tools/lake.py build MachCSL.Machine.ColdBootFacts
```

Both builds passed. Timed fresh module builds measured 2.2 seconds / 2.92 seconds
wall / 1,714,888 KB maximum RSS for `ColdBoot`; 2.5 seconds / 3.25 seconds wall /
1,744,272 KB maximum RSS for the final `ColdBootFacts`. The footprint includes
imports of the actual generated model. Earlier whole-expression conversion hit
the heartbeat limit; whole-state `cbv` took 57 seconds and 2,613,544 KB before its
internal timeout. Factoring the exact projection from its arithmetic removed
that failure without increasing the existing heartbeat budget.

An enforced `Lean.collectAxioms` audit of all seven public boot theorems passed;
each has only `propext`, `Classical.choice`, and `Quot.sound` transitively. No
`sorry`, added axiom, native decision procedure, or `bv_decide` was used.
Reproducible scratch driver and logs from this run are
`/tmp/xv6-lean-research/ColdBootAudit.lean`, `coldboot-axiom-audit.log`,
`coldboot-base-build.log`, and `coldboot-facts-build.log` (temporary paths,
not required repository build inputs).

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
