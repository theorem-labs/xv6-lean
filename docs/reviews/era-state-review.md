# Independent era/register state-update review

Result: **PASS**. Read the complete `EraState{Defs,Spec,Proofs,Link}.lean`
against paper pin `fa7f0a01c4b40489fac8ad303f079c2dfc7a1476`, including
`RiscvPtsto.v:1897–1912` (dependent register-map agreement), `2083–2095`
(per-CPU/device interpretations), `2150–2226` (all era/fixed/trace conjuncts),
and the direct register behavior in `HartRegNode.v:173–251`.

`withRegisters` replaces the actual CPU-to-dependent-register-file
function; `writeRegister` updates the selected actual CPU and generated
register using the existing typed setter. `registers_access` splits the
complete global register interpretation and returns an arbitrary-file
reassembly wand, framing all other six era conjuncts. Those conjuncts do
not inspect registers, which is verified by definitional equalities.
The read theorem obtains its typed equality from authoritative register
agreement at any requested fraction. The write theorem requires the full
old cell and returns the complete new era interpretation and full new
cell. It does not weaken the ownership fraction or use an untyped register
projection. `writeBack_register` proves exact equality to the actual hart
writeback, including unchanged other-CPU fields and views/reservations.

`MachineInterp.live_update` is explicitly conditional on a PROVED era
resource update and preservation of generation, power and durable disk.
These three preservation premises suffice to retain both fixed counters,
the registry domain, and sized durable authority. Actual registry
lookup/agreement identifies the active era with the caller's generation
certificate; the proof does not substitute an arbitrary era record.
The client resource/result parameters permit sound framing around the
proved update. This generic rule is not itself a hardware preservation
claim.

The concrete `power_read_register` and `power_write_register` close all
register-specification premises using the existing checked implementation.
The write wrapper proves the three fixed-state preservation equations by
definitional equality. The independently importable `EraStateSpec` retains
its generic component contract intentionally; `registryEraStateSpec`
links its implementation. No new capacity or runtime name is introduced.

Independently reran `python3 tools/lake.py build
MachCSL.Logic.ResetDiskWPLink MachCSL.Logic.EraStateLink`: 426 jobs passed.
`/tmp/xv6-lean-research/EraStateIndependentAudit.lean` independently audits
all 22 EraState public/private declarations and the three MachineInterp
adapters, including their complete dependency cones. Only `propext`,
`Classical.choice`, and `Quot.sound` are accepted; output is
`era-state-independent-axioms.log`.

No correction was required. These are actual current-era and fixed-state
resource bridges. They do not alone prove WP safety, arbitrary
state-changing operations, disk-changing transitions, or full adequacy.

*Authorship note: this was researched and written by an AI coding agent
(OpenAI Codex), working on Jason Gross's behalf; Jason reviews what is
posted from this account.*
